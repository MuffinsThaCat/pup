#!/usr/bin/env python3
"""Benchmarks for PUP at production parameters (n=16 and n=20)."""

import os
import time
import statistics
from chain_hash_sig import (
    Params, keygen, registration_data, create_account, sign, verify_and_update,
)

def bench(label, fn, warmup=2, trials=20):
    for _ in range(warmup):
        fn()
    times = []
    for _ in range(trials):
        t0 = time.perf_counter()
        fn()
        times.append(time.perf_counter() - t0)
    med = statistics.median(times)
    return med

def run_benchmarks(p, label):
    print(f"\n{'='*60}")
    print(f"  PUP Benchmark: {label} (n={p.n}, w={p.w}, H={p.H})")
    print(f"{'='*60}")

    # Keygen (use smaller H for measurability, then extrapolate)
    small_p = Params(n=p.n, w=p.w, H=10)
    t_keygen_small = bench(
        "keygen", lambda: keygen(small_p), warmup=1, trials=5
    )
    keygen_extrapolated = t_keygen_small * (2 ** p.H / 2 ** small_p.H)
    print(f"  Keygen (H={small_p.H}, measured):  {t_keygen_small*1000:.1f} ms")
    print(f"  Keygen (H={p.H}, extrapolated):  {keygen_extrapolated:.1f} s")

    # Sign and verify at H=10 (production-shape, measurable)
    fk, pk = keygen(small_p, seed=os.urandom(32))
    leaf_hash, auth_0 = registration_data(fk)
    state = create_account(pk, leaf_hash, auth_0)

    # Sign benchmark
    msg = b'benchmark transaction payload 64 bytes of representative data!!'
    t_sign = bench("sign", lambda: sign(fk, msg, 0), warmup=5, trials=50)
    print(f"  Sign:                            {t_sign*1000:.3f} ms")

    # Verify benchmark (sequential, to properly test state update)
    sigs = []
    for i in range(100):
        sigs.append((f'tx-{i}'.encode(), sign(fk, f'tx-{i}'.encode(), i)))

    def verify_batch():
        st = state
        for m, s in sigs[:20]:
            ok, st = verify_and_update(pk, m, s, st)

    t_verify_batch = bench("verify", verify_batch, warmup=2, trials=20)
    t_verify = t_verify_batch / 20
    print(f"  Verify+Update:                   {t_verify*1000:.3f} ms")
    print(f"  Verify throughput:               {1/t_verify:.0f} verifications/s")

    # Signature sizes from real run
    state2 = create_account(pk, leaf_hash, auth_0)
    sizes = []
    for i in range(min(small_p.max_sigs - 1, 512)):
        m = f'tx-{i}'.encode()
        s = sign(fk, m, i)
        sizes.append(s.size_bytes)
        ok, state2 = verify_and_update(pk, m, s, state2)

    avg_size = statistics.mean(sizes)
    print(f"  Signature size (avg):            {avg_size:.0f} bytes")
    print(f"  Signature size (min):            {min(sizes)} bytes")
    print(f"  Signature size (max):            {max(sizes)} bytes")
    print(f"  OTS component:                   {small_p.ots_sig_bytes} bytes")
    print(f"  Avg delta overhead:              {avg_size - small_p.ots_sig_bytes - 4:.0f} bytes")

    # Theoretical comparison
    sphincs_sig = 7856
    print(f"\n  vs SPHINCS+-128s ({sphincs_sig} B):")
    print(f"    Size ratio:    {sphincs_sig / avg_size:.1f}x smaller")
    print(f"    Verify ratio:  ~{2090 / (p.l * (p.w-1)/2 + p.H + 3):.1f}x fewer hashes")

if __name__ == '__main__':
    run_benchmarks(Params(n=16, w=16, H=20), "Compact (NIST-I equivalent)")
    run_benchmarks(Params(n=20, w=16, H=20), "Recommended")
    print()
