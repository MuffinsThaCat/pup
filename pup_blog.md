# PUP: Post-quantum Signatures That Are 13.5x Smaller Than SPHINCS+ (By Letting the Blockchain Do the Work)


**TL;DR:** We designed a post-quantum signature scheme that produces ~580-byte signatures instead of SPHINCS+'s ~7,856 bytes, verifies ~53x faster, and relies on the same hash-only security assumption. The trick: stop treating the blockchain as a dumb pipe and make it a participant in the cryptographic protocol.

---

## The Problem

Post-quantum cryptography has a size problem. The signatures that protect us from quantum computers are *enormous* compared to what we use today:

| Scheme | Signature Size | Assumption |
|--------|---------------|------------|
| ECDSA (current) | 64 bytes | Elliptic curves (quantum-dead) |
| ML-DSA (Dilithium) | 2,420 bytes | Lattices |
| SLH-DSA (SPHINCS+) | 7,856 bytes | Hash functions only |

For blockchains, this matters. Every signature lives on-chain, gets propagated to every node, and gets stored forever. A 122x blowup from ECDSA to SPHINCS+ isn't a rounding error — it's a throughput killer.

The lattice-based schemes (ML-DSA) are smaller, but they rest on assumptions that are younger and less battle-tested than "SHA-256 is hard to invert." For a blockchain that's supposed to secure billions of dollars for decades, hash-only assumptions are the conservative choice.

So the question becomes: **can we get hash-only post-quantum security without paying the SPHINCS+ size tax?**

Yes. But you have to cheat — in exactly the way blockchains let you.

## The Insight Nobody Used

There's a family of hash-based signature schemes that have been around since the 1970s: Merkle trees over one-time signatures (Lamport, Winternitz). They're small, fast, and their security is dead simple. XMSS and LMS are standardized versions of this idea.

They have one fatal flaw: **they're stateful.** Each leaf in the Merkle tree can only sign one message. Use a leaf twice, and an attacker can forge signatures. The signer must maintain perfect state — which leaf was used last — across crashes, backups, VM migrations, and operator error.

This is why SPHINCS+ exists. It's a heroic engineering effort to make hash-based signatures *stateless*, at the cost of a 7,856-byte signature that encodes an entire hypertree of Merkle trees plus a FORS few-time signature layer. All of that machinery exists to avoid trusting the signer to track state.

But here's the thing: **blockchains already track state per account.** Every account has a nonce — a sequential counter that prevents transaction replay. The chain enforces that your nonce goes 0, 1, 2, 3... and rejects anything out of order.

That's exactly the state a Merkle-tree signature scheme needs.

## How PUP Works

**PUP** (Post-quantum Unicity Protocol) co-designs the signature scheme with the blockchain's existing state model. The core idea is three-fold:

### 1. Leaf index = transaction nonce

Each account gets a Merkle tree with 2^20 leaves (~1 million). Leaf *i* holds a W-OTS+ one-time key. When you send your *i*-th transaction, you sign with leaf *i*. The blockchain already enforces sequential nonce usage, so it's impossible to reuse a leaf — the chain won't accept it.

The catastrophic failure mode of stateful signatures (accidental leaf reuse) doesn't just get mitigated. It gets **eliminated by construction.**

### 2. On-chain verifier cache

Here's where it gets interesting. When the chain verifies your signature at leaf *i*, it needs the Merkle authentication path — the H sibling hashes that let you walk from the leaf to the root. In XMSS, the signer sends all H siblings every time.

But the chain already verified leaf *i-1* last time. And it turns out that consecutive leaves share most of their authentication path. The number of siblings that change between leaf *i* and leaf *i+1* is:

```
changed(i+1) = v₂(i+1) + 1
```

where v₂ is the 2-adic valuation (number of trailing zeros in the binary representation). On average, that's 2 siblings — but one of them is *derivable* by the verifier (it's the subtree root computed by walking up from the just-verified leaf).

So the signer only needs to send:

```
delta(i+1) = v₂(i+1)
```

new sibling hashes on average. The average value of v₂ over all integers is exactly 1.

**One hash. That's the average delta. 16 bytes.**

The chain stores the current authentication path (~328 bytes per account) and evolves it with each signature verification. The signer sends only what changed.

### 3. Flat Merkle tree, no hypertree

SPHINCS+ uses a hypertree (a tree of trees) with FORS few-time signatures at the bottom — all to avoid statefulness. Since we've eliminated the statefulness problem, we don't need any of that. One flat Merkle tree. One W-OTS+ per leaf. Done.

## The Numbers

For NIST Level I equivalent security (n=16 bytes, w=16, H=20):

| Metric | SPHINCS+-128s | PUP |
|--------|--------------|------|
| Signature size (avg) | 7,856 B | **~580 B** |
| Signature size (worst) | 7,856 B | **~880 B** |
| Verification speed | baseline | **~53x faster** |
| Security assumption | hash-only | hash-only |
| Quantum security | ~2^54 | ~2^54.9 |
| Reduction tightness | loses 2^(h/d) | **tight** |
| On-chain state | 0 B | 328 B/account |

The ~580 bytes breaks down as:
- W-OTS+ signature: 35 chains × 16 bytes = 560 B
- Leaf index: 4 B  
- Delta (avg 1 sibling): 16 B

For a more comfortable quantum security margin, n=20 gives ~2^70.9 quantum security at ~724 bytes average. Still 10.8x smaller than SPHINCS+.

## Why the Reduction Is Tight (And Why That Matters)

This is subtle but important for cryptographers.

In SPHINCS+, the security proof reduces EU-CMA security to the security of the underlying OTS and hash function. But the reduction isn't tight — it loses a factor of 2^(h/d) because the simulator has to *guess* which subtree the adversary will target. This is inherent to stateless schemes: the adversary can adaptively choose where to attack.

In PUP, the adversary has **zero adaptive choice.** The blockchain state fixes the target leaf to `next_index`. The simulator knows exactly where to embed its challenge. The reduction is tight: if you can break PUP, you can break the hash function with the same advantage.

This means PUP's *proven* security is closer to its *actual* security than SPHINCS+'s is. At the same parameter size, you get more security in practice.

## The Tradeoff

PUP is not a general-purpose signature scheme. It requires:

1. **A blockchain (or equivalent ordered state machine)** that enforces sequential per-account signing and can store ~328 bytes of authentication state per account.

2. **Key rotation every ~1M signatures.** The tree has 2^20 leaves. At one transaction per block (12s blocks), that's ~388 years. At one tx/second, it's ~12 days. High-frequency accounts need key rotation — which is a normal blockchain operation.

3. **Signer maintains the full Merkle tree** (or the seed to regenerate it). This is ~16 MB for H=20, n=16.

If you're not on a blockchain, use SPHINCS+. If you are, you're leaving a 13.5x size reduction on the table.

## Verification

We don't ask you to trust the math on faith. The scheme comes with three test suites totaling 205 tests:

- **84 functional tests** — correctness, edge cases, performance, cross-validation
- **80 security proof tests** — 7 formal theorems with executable verification, including reduction extraction and exhaustive checksum completeness
- **41 exhaustive verification tests** — every claim verified for ALL inputs at tractable parameter sizes, not sampled:
  - Every leaf transition in a 256-leaf tree: correct
  - Every single-byte mutation of every signature: rejected
  - Every replay at every state: rejected  
  - Every cross-leaf signature forgery: rejected
  - Delta formula vs brute-force for all indices up to 2^16: exact match
  - Checksum property for all 16.8M message pairs: holds
  - All address tweaks across all hash call sites: unique

The only unverifiable assumption is that SHA-256 is a secure hash function. Given that, every claim the scheme makes is exhaustively proven.

## The Construction in One Paragraph

**Key generation:** Generate a seed. Derive 2^H W-OTS+ key pairs via PRF. Hash each public key to get a leaf. Build a Merkle tree. The root is your public key. **Registration:** Submit leaf 0's hash and authentication path to the chain; the chain verifies it against your root and caches the auth path. **Signing:** Sign message with W-OTS+ at leaf `next_index`. Compute the delta (changed sibling hashes for the next transition). **Verification:** The chain recovers the leaf hash from the W-OTS+ signature, walks up the Merkle tree using its cached authentication path, checks it hits the root, then updates its cached path using the delta plus one derived sibling. Advance `next_index`.

## What's Next

The scheme is implemented in Python as a reference. The natural next steps are:

1. **Constant-time C/Rust implementation** for production use
2. **EVM precompile or protocol-level integration** in a blockchain
3. **Formal security proof** in the QROM (quantum random oracle model) for publication
4. **Tree compaction** — the signer doesn't need to store the full tree; it can regenerate branches on demand from the seed

The code is open. The math is tested. The 13.5x signature compression is real.

---

*PUP: Post-quantum Unicity Protocol. Built on the observation that blockchains already solve the hardest problem in stateful cryptography — they just didn't know it.*
