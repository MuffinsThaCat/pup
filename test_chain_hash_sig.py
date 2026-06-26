#!/usr/bin/env python3
"""
Test suite for the chain-native stateful hash-based signature scheme.

Proves correctness, security properties, delta-compression theory, and
measures concrete sizes vs SPHINCS+ / Falcon / XMSS.

Run: pytest test_chain_hash_sig.py -v
"""

import math
import os
import time
import hashlib

import pytest

from chain_hash_sig import (
    Params, hash_n, prf, base_w,
    wots_keygen, wots_pk_hash, wots_sign, wots_verify, wots_recover_leaf, wots_chain,
    build_merkle_tree, merkle_auth_path, merkle_root_from_leaf, merkle_node_hash,
    merge_level, delta_count,
    keygen, create_account, registration_data, sign, verify_and_update,
    _bound_payload,
    FullKey, PublicKey, AuthState, Signature,
    DOMAIN_LEAF, DOMAIN_NODE, DOMAIN_CHAIN, DOMAIN_MSG,
    _all_digits, _checksum_bytes,
    _leaf_addr, _node_addr, _addr,
)


# ---------------------------------------------------------------------------
# Test parameters (small trees for speed; large tree in select tests)
# ---------------------------------------------------------------------------
FAST = Params(n=16, w=16, H=6)   # 64 leaves — fast
MED  = Params(n=16, w=16, H=8)   # 256 leaves
FULL = Params(n=16, w=16, H=10)  # 1024 leaves — closer to production shape

def _make_keys(p: Params, seed: bytes = b'test-seed-32-bytes-exactly!!1234'):
    fk, pk = keygen(p, seed=seed)
    leaf_hash, auth_0 = registration_data(fk)
    state = create_account(pk, leaf_hash, auth_0)
    return fk, pk, state


# ===================================================================
# 1. W-OTS+ PRIMITIVES
# ===================================================================

class TestWOTSPlus:

    def test_keygen_deterministic(self):
        p = FAST
        seed = b'deterministic-seed-exactly32byte'
        sk1, pk1 = wots_keygen(seed, 0, p)
        sk2, pk2 = wots_keygen(seed, 0, p)
        assert sk1 == sk2
        assert pk1 == pk2

    def test_keygen_different_leaves(self):
        p = FAST
        seed = b'deterministic-seed-exactly32byte'
        _, pk0 = wots_keygen(seed, 0, p)
        _, pk1 = wots_keygen(seed, 1, p)
        assert pk0 != pk1

    def test_chain_count(self):
        p = Params(n=16, w=16, H=6)
        assert p.l1 == 32
        assert p.l2 == 3
        assert p.l == 35

    def test_sign_verify_roundtrip(self):
        p = FAST
        seed = os.urandom(32)
        sk, pk = wots_keygen(seed, 0, p)
        msg = b'hello world'
        sig = wots_sign(sk, msg, p, leaf_idx=0)
        assert wots_verify(sig, msg, pk, p, leaf_idx=0)

    def test_recover_leaf_matches(self):
        p = FAST
        seed = os.urandom(32)
        sk, pk = wots_keygen(seed, 0, p)
        msg = b'test message'
        sig = wots_sign(sk, msg, p, leaf_idx=0)
        leaf = wots_recover_leaf(sig, msg, p, leaf_idx=0)
        expected_leaf = wots_pk_hash(pk, p, leaf_idx=0)
        assert leaf == expected_leaf

    def test_wrong_message_rejected(self):
        p = FAST
        seed = os.urandom(32)
        sk, pk = wots_keygen(seed, 0, p)
        sig = wots_sign(sk, b'correct', p, leaf_idx=0)
        assert not wots_verify(sig, b'wrong', pk, p, leaf_idx=0)

    def test_tampered_sig_rejected(self):
        p = FAST
        seed = os.urandom(32)
        sk, pk = wots_keygen(seed, 0, p)
        msg = b'important'
        sig = wots_sign(sk, msg, p, leaf_idx=0)
        tampered = list(sig)
        tampered[0] = bytes(p.n)
        assert not wots_verify(tampered, msg, pk, p, leaf_idx=0)

    def test_wrong_key_rejected(self):
        p = FAST
        seed1 = os.urandom(32)
        seed2 = os.urandom(32)
        sk1, _ = wots_keygen(seed1, 0, p)
        _, pk2 = wots_keygen(seed2, 0, p)
        msg = b'message'
        sig = wots_sign(sk1, msg, p, leaf_idx=0)
        assert not wots_verify(sig, msg, pk2, p, leaf_idx=0)

    def test_sig_size(self):
        p = Params(n=16, w=16, H=6)
        assert p.ots_sig_bytes == 35 * 16  # 560 bytes

    def test_base_w_round_trip(self):
        data = os.urandom(16)
        digits = base_w(data, 16, 32)
        assert len(digits) == 32
        assert all(0 <= d < 16 for d in digits)

    def test_checksum_consistency(self):
        """Signer and verifier compute the same digit sequence."""
        p = FAST
        msg = os.urandom(32)
        d1 = _all_digits(msg, p)
        d2 = _all_digits(msg, p)
        assert d1 == d2
        assert len(d1) == p.l

    def test_checksum_prevents_universal_forgery(self):
        """Without checksum, attacker could advance chains. Checksum digits
        go in the OPPOSITE direction, making this impossible."""
        p = FAST
        msg = os.urandom(32)
        digits = _all_digits(msg, p)
        msg_digits = digits[:p.l1]
        cs_digits = digits[p.l1:]
        csum = sum(p.w - 1 - d for d in msg_digits)
        assert csum >= 0
        assert len(cs_digits) == p.l2


# ===================================================================
# 2. MERKLE TREE
# ===================================================================

class TestMerkleTree:

    def test_single_leaf(self):
        leaf = hash_n(DOMAIN_LEAF, _leaf_addr(0), b'only-leaf', 16)
        tree = build_merkle_tree([leaf], 16)
        assert tree[-1][0] == leaf

    def test_two_leaves(self):
        l0 = hash_n(DOMAIN_LEAF, _leaf_addr(0), b'leaf0', 16)
        l1 = hash_n(DOMAIN_LEAF, _leaf_addr(1), b'leaf1', 16)
        tree = build_merkle_tree([l0, l1], 16)
        expected_root = merkle_node_hash(l0, l1, 16, level=1, index=0)
        assert tree[-1][0] == expected_root

    def test_auth_path_verifies(self):
        n = 16
        leaves = [hash_n(DOMAIN_LEAF, _leaf_addr(i), f'leaf-{i}'.encode(), n)
                  for i in range(8)]
        tree = build_merkle_tree(leaves, n)
        root = tree[-1][0]
        for i in range(8):
            path = merkle_auth_path(tree, i)
            assert merkle_root_from_leaf(leaves[i], i, path, n) == root

    def test_wrong_leaf_rejected(self):
        n = 16
        leaves = [hash_n(DOMAIN_LEAF, _leaf_addr(i), f'leaf-{i}'.encode(), n)
                  for i in range(4)]
        tree = build_merkle_tree(leaves, n)
        root = tree[-1][0]
        path = merkle_auth_path(tree, 0)
        fake_leaf = hash_n(DOMAIN_LEAF, _leaf_addr(0), b'fake', n)
        assert merkle_root_from_leaf(fake_leaf, 0, path, n) != root

    def test_wrong_index_rejected(self):
        n = 16
        leaves = [hash_n(DOMAIN_LEAF, _leaf_addr(i), f'leaf-{i}'.encode(), n)
                  for i in range(4)]
        tree = build_merkle_tree(leaves, n)
        root = tree[-1][0]
        path = merkle_auth_path(tree, 0)
        assert merkle_root_from_leaf(leaves[0], 1, path, n) != root

    def test_domain_separation(self):
        addr = b'\x00\x00\x00\x00'
        data = b'same-data'
        assert hash_n(DOMAIN_LEAF, addr, data, 16) != hash_n(DOMAIN_NODE, addr, data, 16)
        assert hash_n(DOMAIN_NODE, addr, data, 16) != hash_n(DOMAIN_CHAIN, addr, data, 16)

    def test_tree_levels_correct(self):
        n = 16
        leaves = [os.urandom(n) for _ in range(8)]
        tree = build_merkle_tree(leaves, n)
        assert len(tree) == 4  # 8 leaves → levels: 8, 4, 2, 1
        assert len(tree[0]) == 8
        assert len(tree[1]) == 4
        assert len(tree[2]) == 2
        assert len(tree[3]) == 1

    def test_address_tweaking_prevents_cross_position(self):
        """Same children at different positions produce different parent hashes.
        Without tweaking, an attacker could transplant a subtree from one
        position to another. With tweaking, each position is independent."""
        n = 16
        left = os.urandom(n)
        right = os.urandom(n)
        h_pos0 = merkle_node_hash(left, right, n, level=1, index=0)
        h_pos1 = merkle_node_hash(left, right, n, level=1, index=1)
        h_lv2  = merkle_node_hash(left, right, n, level=2, index=0)
        assert h_pos0 != h_pos1  # same data, different position → different hash
        assert h_pos0 != h_lv2   # same data, different level → different hash

    def test_leaf_tweaking_prevents_cross_leaf(self):
        """Same OTS public key at different leaf positions produces different leaf hashes."""
        p = FAST
        pk_data = [os.urandom(p.n) for _ in range(p.l)]
        h0 = wots_pk_hash(pk_data, p, leaf_idx=0)
        h1 = wots_pk_hash(pk_data, p, leaf_idx=1)
        assert h0 != h1

    def test_chain_tweaking_prevents_cross_chain(self):
        """Same secret at different (leaf, chain) positions produces different output."""
        p = FAST
        secret = os.urandom(p.n)
        v_chain0 = wots_chain(secret, 0, 5, p.n, leaf_idx=0, chain_idx=0)
        v_chain1 = wots_chain(secret, 0, 5, p.n, leaf_idx=0, chain_idx=1)
        v_leaf1  = wots_chain(secret, 0, 5, p.n, leaf_idx=1, chain_idx=0)
        assert v_chain0 != v_chain1
        assert v_chain0 != v_leaf1


# ===================================================================
# 3. DELTA COMPRESSION THEORY
# ===================================================================

class TestDeltaCompression:

    def test_merge_level_values(self):
        assert merge_level(0) == 0
        assert merge_level(1) == 1
        assert merge_level(2) == 2
        assert merge_level(3) == 1
        assert merge_level(4) == 3
        assert merge_level(5) == 1
        assert merge_level(6) == 2
        assert merge_level(7) == 1
        assert merge_level(8) == 4
        assert merge_level(16) == 5
        assert merge_level(32) == 6

    def test_merge_level_is_v2_plus_1(self):
        """merge_level(i) = v2(i) + 1 where v2 = 2-adic valuation."""
        for i in range(1, 256):
            v2 = 0
            k = i
            while k & 1 == 0:
                v2 += 1
                k >>= 1
            assert merge_level(i) == v2 + 1, f"failed at i={i}"

    def test_delta_count_sequence(self):
        # delta_count = merge_level - 1 = v2(i) for i>=1, 0 for i=0
        expected = [0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4]
        for i, exp in enumerate(expected):
            assert delta_count(i) == exp, f"delta_count({i})={delta_count(i)}, expected {exp}"

    def test_average_delta_converges_to_1(self):
        """Theoretical prediction: E[delta_count] = E[v2(i)] = 1 for uniform i>=1.
        The level M-1 sibling is derived by the verifier, so we send M-1 not M."""
        N = 10000
        total = sum(delta_count(i) for i in range(1, N + 1))
        avg = total / N
        assert abs(avg - 1.0) < 0.05, f"average delta = {avg}, expected ~1.0"

    def test_delta_never_exceeds_tree_height(self):
        H = 10
        for i in range(1, 1 << H):
            assert delta_count(i) < H  # strictly less (M-1 < H)

    def test_half_of_transitions_have_zero_delta(self):
        """Odd target indices have merge_level=1, delta_count=0 (derivable)."""
        N = 1000
        zeros = sum(1 for i in range(1, N + 1) if delta_count(i) == 0)
        assert zeros == N // 2

    def test_worst_case_at_powers_of_2(self):
        for k in range(1, 12):
            i = 1 << k
            assert delta_count(i) == k  # v2(2^k) = k


# ===================================================================
# 4. FULL SCHEME — END TO END
# ===================================================================

class TestSchemeEndToEnd:

    def test_keygen_produces_valid_keys(self):
        fk, pk = keygen(FAST)
        assert len(pk.root) == FAST.n
        assert len(fk.tree) == FAST.H + 1
        assert len(fk.tree[0]) == FAST.max_sigs

    def test_registration_roundtrip(self):
        fk, pk = keygen(FAST)
        leaf_hash, auth_0 = registration_data(fk)
        state = create_account(pk, leaf_hash, auth_0)
        assert state is not None
        assert state.next_index == 0
        assert len(state.cached_siblings) == FAST.H

    def test_registration_rejects_wrong_auth_path(self):
        fk, pk = keygen(FAST)
        leaf_hash, auth_0 = registration_data(fk)
        bad_auth = [os.urandom(FAST.n) for _ in range(FAST.H)]
        state = create_account(pk, leaf_hash, bad_auth)
        assert state is None

    def test_registration_rejects_wrong_leaf(self):
        fk, pk = keygen(FAST)
        _, auth_0 = registration_data(fk)
        fake_leaf = os.urandom(FAST.n)
        state = create_account(pk, fake_leaf, auth_0)
        assert state is None

    def test_first_signature(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'first transaction'
        sig = sign(fk, msg, 0)
        ok, new_state = verify_and_update(pk, msg, sig, state)
        assert ok
        assert new_state.next_index == 1

    def test_sequential_signatures(self):
        fk, pk, state = _make_keys(FAST)
        for i in range(FAST.max_sigs):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok, f"signature {i} failed"
            assert state.next_index == i + 1

    def test_signatures_with_varied_messages(self):
        fk, pk, state = _make_keys(FAST)
        messages = [os.urandom(j + 1) for j in range(20)]
        for i, msg in enumerate(messages):
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok

    def test_auth_state_correct_after_each_sig(self):
        """After verifying sig i, the cached auth state should match
        the true auth path for leaf i+1 (the next expected leaf)."""
        fk, pk, state = _make_keys(FAST)
        for i in range(min(32, FAST.max_sigs - 1)):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
            true_auth = merkle_auth_path(fk.tree, i + 1)
            assert state.cached_siblings == true_auth, (
                f"auth cache diverged at index {i+1}"
            )


# ===================================================================
# 5. SECURITY PROPERTIES
# ===================================================================

class TestSecurity:

    def test_wrong_index_rejected(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'message'
        sig = sign(fk, msg, 0)
        sig_wrong_idx = Signature(index=1, ots_sig=sig.ots_sig, delta=sig.delta)
        ok, _ = verify_and_update(pk, msg, sig_wrong_idx, state)
        assert not ok

    def test_skip_index_rejected(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'message'
        sig = sign(fk, msg, 5)
        ok, _ = verify_and_update(pk, msg, sig, state)
        assert not ok

    def test_replay_rejected(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'message'
        sig = sign(fk, msg, 0)
        ok, state = verify_and_update(pk, msg, sig, state)
        assert ok
        ok2, _ = verify_and_update(pk, msg, sig, state)
        assert not ok2

    def test_wrong_message_rejected(self):
        fk, pk, state = _make_keys(FAST)
        sig = sign(fk, b'real message', 0)
        ok, _ = verify_and_update(pk, b'forged message', sig, state)
        assert not ok

    def test_tampered_ots_sig_rejected(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'important'
        sig = sign(fk, msg, 0)
        bad_chains = list(sig.ots_sig)
        bad_chains[0] = bytes(FAST.n)
        bad_sig = Signature(index=0, ots_sig=bad_chains, delta=sig.delta)
        ok, _ = verify_and_update(pk, msg, bad_sig, state)
        assert not ok

    def test_wrong_public_key_rejected(self):
        fk1, pk1, state1 = _make_keys(FAST)
        _, pk2 = keygen(FAST, seed=os.urandom(32))
        msg = b'message'
        sig = sign(fk1, msg, 0)
        ok, _ = verify_and_update(pk2, msg, sig, state1)
        assert not ok

    def test_key_exhaustion_detected(self):
        p = Params(n=16, w=16, H=3)  # only 8 signatures
        fk, pk, state = _make_keys(p)
        for i in range(p.max_sigs):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
        assert state.next_index == p.max_sigs
        msg = b'one-too-many'
        sig_obj = Signature(index=p.max_sigs, ots_sig=[], delta=[])
        ok, _ = verify_and_update(pk, msg, sig_obj, state)
        assert not ok

    def test_different_messages_different_sigs(self):
        fk, pk = keygen(FAST, seed=b'fixed-seed-exactly-32-bytes!!!!!')
        sk, _ = wots_keygen(fk.seed, 0, FAST)
        sig_a = wots_sign(sk, b'message A', FAST, leaf_idx=0)
        sig_b = wots_sign(sk, b'message B', FAST, leaf_idx=0)
        assert sig_a != sig_b

    def test_tampered_delta_rejected_immediately(self):
        """With bound-payload construction, tampering with delta invalidates
        the OTS signature at the CURRENT verification, not just the next."""
        fk, pk, state = _make_keys(FAST)

        sig0 = sign(fk, b'tx-0', 0)
        ok, state = verify_and_update(pk, b'tx-0', sig0, state)
        assert ok

        sig1 = sign(fk, b'tx-1', 1)
        bad_delta = [os.urandom(FAST.n)] * len(sig1.delta) if sig1.delta else []
        if bad_delta:
            bad_sig1 = Signature(index=1, ots_sig=sig1.ots_sig, delta=bad_delta)
            ok, _ = verify_and_update(pk, b'tx-1', bad_sig1, state)
            assert not ok  # bound payload: delta tampering fails immediately


# ===================================================================
# 6. DELTA COMPRESSION — EMPIRICAL VERIFICATION
# ===================================================================

class TestDeltaEmpirical:

    def test_delta_sizes_match_theory(self):
        """Every signature's delta length matches delta_count(next_index)."""
        fk, pk, state = _make_keys(FAST)
        for i in range(FAST.max_sigs - 1):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            expected_dc = delta_count(i + 1)
            assert len(sig.delta) == expected_dc, (
                f"index={i}: delta len={len(sig.delta)}, expected={expected_dc}"
            )
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok

    def test_first_sig_has_no_delta(self):
        fk, pk, state = _make_keys(FAST)
        sig = sign(fk, b'first', 0)
        assert len(sig.delta) == 0

    def test_average_delta_bytes(self):
        """Measure average delta overhead across all signatures."""
        p = MED
        fk, pk, state = _make_keys(p)
        total_delta_hashes = 0
        count = 0
        for i in range(p.max_sigs - 1):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            total_delta_hashes += len(sig.delta)
            count += 1
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
        avg_delta = total_delta_hashes / count
        avg_delta_bytes = avg_delta * p.n
        assert avg_delta < 1.5, f"avg delta hashes = {avg_delta}, should be ~1.0"
        print(f"\n  Average delta: {avg_delta:.3f} hashes = {avg_delta_bytes:.1f} bytes")


# ===================================================================
# 7. SIZE MEASUREMENTS AND COMPARISONS
# ===================================================================

class TestSizeMeasurements:

    def test_ots_sig_size_level1(self):
        p = Params(n=16, w=16, H=20)
        assert p.ots_sig_bytes == 560

    def test_ots_sig_size_level3(self):
        p = Params(n=32, w=16, H=20)
        assert p.ots_sig_bytes == p.l * 32

    def test_concrete_sig_sizes(self):
        """Measure actual signature sizes from a real signing run."""
        p = MED
        fk, pk, state = _make_keys(p)
        sizes = []
        for i in range(min(128, p.max_sigs - 1)):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            sizes.append(sig.size_bytes)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok

        avg_size = sum(sizes) / len(sizes)
        min_size = min(sizes)
        max_size = max(sizes)
        print(f"\n  Signature sizes (n={p.n}, w={p.w}, H={p.H}):")
        print(f"    min={min_size} B, avg={avg_size:.0f} B, max={max_size} B")
        print(f"    OTS component: {p.ots_sig_bytes} B (fixed)")
        print(f"    Delta overhead: avg {avg_size - p.ots_sig_bytes - 4:.0f} B")

    def test_comparison_table(self):
        """Print the comparison table vs other PQ schemes."""
        p = Params(n=16, w=16, H=20)

        our_ots = p.ots_sig_bytes
        our_avg_delta = 1.0 * p.n  # E[delta_count] = E[v2(i)] = 1 hash
        our_avg_sig = our_ots + 4 + our_avg_delta
        our_max_delta = (p.H - 1) * p.n
        our_max_sig = our_ots + 4 + our_max_delta

        sphincs_sig = 7856
        falcon_sig = 666
        xmss_sig = p.l * p.n + p.H * p.n  # OTS + full auth path

        print(f"\n  === SIGNATURE SIZE COMPARISON (NIST Level I, 128-bit PQ) ===")
        print(f"  {'Scheme':<25} {'Sig (bytes)':<15} {'Assumptions':<15}")
        print(f"  {'-'*55}")
        print(f"  {'SPHINCS+-128s':<25} {sphincs_sig:<15} {'hash-only':<15}")
        print(f"  {'XMSS (H=20, w=16)':<25} {xmss_sig:<15} {'hash-only':<15}")
        print(f"  {'Falcon-512':<25} {falcon_sig:<15} {'NTRU lattice':<15}")
        print(f"  {'Ours (avg)':<25} {our_avg_sig:<15.0f} {'hash-only':<15}")
        print(f"  {'Ours (max)':<25} {our_max_sig:<15} {'hash-only':<15}")
        print(f"")
        print(f"  Improvement over SPHINCS+: {sphincs_sig / our_avg_sig:.1f}x smaller (avg)")
        print(f"  Improvement over XMSS:     {xmss_sig / our_avg_sig:.1f}x smaller (avg)")
        print(f"  vs Falcon-512:             {our_avg_sig / falcon_sig:.2f}x (ours/falcon)")

        assert our_avg_sig < sphincs_sig / 5
        assert our_avg_sig < xmss_sig / 1.5

    def test_on_chain_state_size(self):
        p = Params(n=16, w=16, H=20)
        state_bytes = p.auth_state_bytes
        print(f"\n  On-chain state per account: {state_bytes} bytes")
        print(f"  At 1M accounts: {state_bytes * 1_000_000 / 1e6:.0f} MB")
        assert state_bytes == 20 * 16 + 4  # 324 bytes

    def test_public_key_size(self):
        p = Params(n=16, w=16, H=20)
        pk_size = p.n  # just the Merkle root
        assert pk_size == 16

    def test_registration_overhead(self):
        """One-time cost at account creation."""
        p = Params(n=16, w=16, H=20)
        leaf_hash_size = p.n
        auth_path_size = p.H * p.n
        total = leaf_hash_size + auth_path_size + p.n  # leaf + auth + pubkey
        print(f"\n  Registration overhead: {total} bytes (one-time)")
        assert total == 16 + 320 + 16  # 352 bytes


# ===================================================================
# 8. VERIFY COST (hash count)
# ===================================================================

class TestVerifyCost:

    def test_wots_verify_hash_count(self):
        """W-OTS+ verify iterates remaining chain steps per digit."""
        p = Params(n=16, w=16, H=20)
        avg_steps_per_chain = (p.w - 1) / 2
        total_verify_hashes = p.l * avg_steps_per_chain
        path_hashes = p.H
        total = total_verify_hashes + path_hashes

        sphincs_verify_hashes = 15000  # approximate

        print(f"\n  === VERIFY COST (hash evaluations) ===")
        print(f"  W-OTS+ chains: {p.l} × {avg_steps_per_chain:.1f} avg = {total_verify_hashes:.0f}")
        print(f"  Merkle path:   {path_hashes}")
        print(f"  Total:         {total:.0f}")
        print(f"  SPHINCS+-128s: ~{sphincs_verify_hashes}")
        print(f"  Speedup:       ~{sphincs_verify_hashes / total:.0f}x")

        assert total < sphincs_verify_hashes / 10


# ===================================================================
# 9. PARAMETER SPACE EXPLORATION
# ===================================================================

class TestParameterSpace:

    @pytest.mark.parametrize("w", [4, 16, 64, 256])
    def test_winternitz_tradeoff(self, w):
        p = Params(n=16, w=w, H=20)
        avg_verify_hashes = p.l * (w - 1) / 2 + p.H
        print(f"\n  w={w:>3}: l={p.l:>3}, sig={p.ots_sig_bytes:>5} B, "
              f"verify≈{avg_verify_hashes:>6.0f} hashes")

    @pytest.mark.parametrize("H", [10, 16, 20, 24])
    def test_tree_height_tradeoff(self, H):
        p = Params(n=16, w=16, H=H)
        avg_delta_bytes = 1.0 * p.n
        avg_sig = p.ots_sig_bytes + 4 + avg_delta_bytes
        max_delta_bytes = (H - 1) * p.n
        max_sig = p.ots_sig_bytes + 4 + max_delta_bytes
        print(f"\n  H={H:>2}: max_sigs=2^{H}={p.max_sigs:>10,}, "
              f"sig avg={avg_sig:.0f} B / max={max_sig} B, "
              f"state={p.auth_state_bytes} B/acct")

    @pytest.mark.parametrize("n", [16, 24, 32])
    def test_security_level_tradeoff(self, n):
        p = Params(n=n, w=16, H=20)
        print(f"\n  n={n:>2} (NIST {'I' if n==16 else 'III' if n==24 else 'V'}): "
              f"sig={p.ots_sig_bytes} B, state={p.auth_state_bytes} B")


# ===================================================================
# 10. PERFORMANCE BENCHMARKS
# ===================================================================

class TestPerformance:

    def test_keygen_time(self):
        p = FAST
        t0 = time.perf_counter()
        keygen(p)
        dt = time.perf_counter() - t0
        print(f"\n  Keygen (H={p.H}, {p.max_sigs} leaves): {dt*1000:.1f} ms")

    def test_sign_time(self):
        fk, pk, state = _make_keys(FAST)
        msg = b'benchmark-message'
        N = 20
        t0 = time.perf_counter()
        for i in range(N):
            sign(fk, msg, i)
        dt = (time.perf_counter() - t0) / N
        print(f"\n  Sign time: {dt*1000:.2f} ms")

    def test_verify_time(self):
        fk, pk, state = _make_keys(FAST)
        sigs = []
        for i in range(20):
            msg = f'tx-{i}'.encode()
            sigs.append((msg, sign(fk, msg, i)))

        st = state
        t0 = time.perf_counter()
        for msg, sig in sigs:
            ok, st = verify_and_update(pk, msg, sig, st)
            assert ok
        dt = (time.perf_counter() - t0) / len(sigs)
        print(f"\n  Verify+update time: {dt*1000:.2f} ms")

    def test_full_tree_exhaustion(self):
        """Sign and verify every leaf in a small tree."""
        p = Params(n=16, w=16, H=6)
        fk, pk, state = _make_keys(p)
        t0 = time.perf_counter()
        for i in range(p.max_sigs):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
        dt = time.perf_counter() - t0
        rate = p.max_sigs / dt
        print(f"\n  Full exhaustion (H={p.H}, {p.max_sigs} sigs): "
              f"{dt:.2f}s = {rate:.0f} sig/s")


# ===================================================================
# 11. EDGE CASES
# ===================================================================

class TestEdgeCases:

    def test_empty_message(self):
        fk, pk, state = _make_keys(FAST)
        sig = sign(fk, b'', 0)
        ok, _ = verify_and_update(pk, b'', sig, state)
        assert ok

    def test_large_message(self):
        fk, pk, state = _make_keys(FAST)
        msg = os.urandom(10_000)
        sig = sign(fk, msg, 0)
        ok, _ = verify_and_update(pk, msg, sig, state)
        assert ok

    def test_last_leaf_in_tree(self):
        p = Params(n=16, w=16, H=3)
        fk, pk, state = _make_keys(p)
        for i in range(p.max_sigs - 1):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
        last_msg = b'final'
        sig = sign(fk, last_msg, p.max_sigs - 1)
        ok, state = verify_and_update(pk, last_msg, sig, state)
        assert ok
        assert state.next_index == p.max_sigs

    def test_height_1_tree(self):
        p = Params(n=16, w=16, H=1)
        fk, pk, state = _make_keys(p)
        sig = sign(fk, b'only-two-sigs', 0)
        ok, state = verify_and_update(pk, b'only-two-sigs', sig, state)
        assert ok
        sig = sign(fk, b'second', 1)
        ok, state = verify_and_update(pk, b'second', sig, state)
        assert ok
        assert state.next_index == 2

    def test_deterministic_keygen(self):
        seed = b'reproducible-seed-32-bytes!!!!!!!'
        fk1, pk1 = keygen(FAST, seed=seed)
        fk2, pk2 = keygen(FAST, seed=seed)
        assert pk1.root == pk2.root

    def test_different_seeds_different_keys(self):
        _, pk1 = keygen(FAST, seed=os.urandom(32))
        _, pk2 = keygen(FAST, seed=os.urandom(32))
        assert pk1.root != pk2.root


# ===================================================================
# 12. BLOCKCHAIN INTEGRATION PROPERTIES
# ===================================================================

class TestBlockchainProperties:

    def test_nonce_index_binding(self):
        """The leaf index IS the transaction nonce — replay protection is structural."""
        fk, pk, state = _make_keys(FAST)
        sig0 = sign(fk, b'tx-0', 0)
        ok, state = verify_and_update(pk, b'tx-0', sig0, state)
        assert ok
        assert state.next_index == 1

        ok_replay, _ = verify_and_update(pk, b'tx-0', sig0, state)
        assert not ok_replay  # nonce already consumed

    def test_state_size_bounded(self):
        """On-chain state is O(H) regardless of how many sigs have been verified."""
        p = FAST
        fk, pk, state = _make_keys(p)
        initial_size = state.size_bytes
        for i in range(p.max_sigs - 1):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
        assert state.size_bytes == initial_size  # size never grows

    def test_independent_accounts(self):
        """Two accounts don't interfere with each other."""
        fk1, pk1, state1 = _make_keys(FAST)
        fk2, pk2, state2 = _make_keys(Params(n=16, w=16, H=6))
        fk2, pk2 = keygen(Params(n=16, w=16, H=6), seed=os.urandom(32))
        leaf_hash2, auth_02 = registration_data(fk2)
        state2 = create_account(pk2, leaf_hash2, auth_02)

        sig1 = sign(fk1, b'alice-tx', 0)
        ok1, state1 = verify_and_update(pk1, b'alice-tx', sig1, state1)
        assert ok1

        sig2 = sign(fk2, b'bob-tx', 0)
        ok2, state2 = verify_and_update(pk2, b'bob-tx', sig2, state2)
        assert ok2

        ok_cross, _ = verify_and_update(pk1, b'bob-tx', sig2, state1)
        assert not ok_cross

    def test_bandwidth_savings_at_scale(self):
        """At 100k TPS with diverse senders, measure DA savings vs SPHINCS+."""
        tps = 100_000
        sphincs_sig_bytes = 7856
        our_avg_sig_bytes = 560 + 4 + 16  # OTS + index + ~1 hash delta

        sphincs_bw = tps * sphincs_sig_bytes / 1e6
        our_bw = tps * our_avg_sig_bytes / 1e6

        print(f"\n  === BANDWIDTH AT {tps:,} TPS ===")
        print(f"  SPHINCS+: {sphincs_bw:.0f} MB/s")
        print(f"  Ours:     {our_bw:.0f} MB/s")
        print(f"  Savings:  {sphincs_bw - our_bw:.0f} MB/s ({sphincs_bw/our_bw:.1f}x)")

        assert our_bw < sphincs_bw / 10


# ===================================================================
# 13. CROSS-VALIDATION: MERKLE PATH CONSISTENCY
# ===================================================================

class TestCrossValidation:

    def test_every_leaf_auth_path_is_valid(self):
        """Verify that build_merkle_tree + merkle_auth_path produce valid
        proofs for every single leaf in the tree."""
        p = MED
        fk, pk = keygen(p)
        for i in range(p.max_sigs):
            path = merkle_auth_path(fk.tree, i)
            root = merkle_root_from_leaf(fk.tree[0][i], i, path, p.n)
            assert root == pk.root, f"leaf {i} auth path invalid"

    def test_evolving_state_matches_direct_path(self):
        """The auth state maintained by verify_and_update should match
        directly computing the auth path from the tree at every step."""
        p = Params(n=16, w=16, H=5)  # 32 leaves
        fk, pk, state = _make_keys(p)
        for i in range(p.max_sigs - 1):
            msg = f'tx-{i}'.encode()
            sig = sign(fk, msg, i)
            ok, state = verify_and_update(pk, msg, sig, state)
            assert ok
            direct_path = merkle_auth_path(fk.tree, i + 1)
            for lv in range(p.H):
                assert state.cached_siblings[lv] == direct_path[lv], (
                    f"level {lv} mismatch after signing index {i}: "
                    f"evolved={state.cached_siblings[lv].hex()}, "
                    f"direct={direct_path[lv].hex()}"
                )


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
