# POOP: Post-quantum Optimized On-chain Protocol

A post-quantum signature scheme that produces **~580-byte signatures** (vs SPHINCS+ ~7,856B) under hash-only assumptions, by co-designing with blockchain state.

## Key Results

- **13.5x smaller** signatures than SPHINCS+-128s
- **~53x faster** verification
- **Same assumption**: hash function security only (no lattices)
- **Tight security reduction** (no 2^(h/d) loss — the blockchain fixes the target leaf)
- **285 tests**, including exhaustive verification of every claim

## How It Works

Blockchains already enforce sequential per-account nonces. POOP binds the signature leaf index to the transaction nonce, eliminating the catastrophic leaf-reuse weakness of stateful hash-based signatures. The chain caches each account's Merkle authentication path (~328 bytes) and the signer sends only the delta — an average of one hash (16 bytes) per signature.

## Files

- `chain_hash_sig.py` — Reference implementation
- `test_chain_hash_sig.py` — 84 functional tests
- `proof_chain_hash_sig.py` — 80 security proof tests (7 theorems)
- `verify_exhaustive.py` — 41 exhaustive verification tests
- `poop_blog.md` — Blog post explaining the scheme

## Run Tests

```bash
pip install pytest
pytest -v
```

## Parameters

Default (NIST Level I equivalent): n=16, w=16, H=20

- Quantum security: ~2^54.9
- Avg signature: ~580 bytes
- On-chain state: 328 bytes/account
- Max signatures/key: ~1M (2^20)

For stronger security: n=20 gives ~2^70.9 quantum security at ~724 bytes avg.

## License

MIT
