#!/usr/bin/env python3
"""
PUP — Post-quantum Unicity Protocol.

A post-quantum signature construction that co-designs with blockchain state
to achieve ~580-byte signatures (vs SPHINCS+ ~7856B) under hash-only assumptions.

Core innovations:
  1. Blockchain-enforced sequential leaf usage eliminates stateful-sig catastrophe
  2. On-chain verifier cache enables delta-compressed authentication paths
  3. Leaf index = transaction nonce (dual-purpose: replay protection + sig state)

Construction: W-OTS+ one-time signatures in a Merkle tree, with the chain
maintaining per-account authentication state across sequential verifications.
"""

import hashlib
import hmac
import math
import os
from dataclasses import dataclass, field
from typing import Optional

# ---------------------------------------------------------------------------
# Domain separation tags (four domains, per Section 2.1)
# ---------------------------------------------------------------------------
DOMAIN_LEAF  = b'\x00'
DOMAIN_NODE  = b'\x01'
DOMAIN_CHAIN = b'\x02'
DOMAIN_MSG   = b'\x03'

# ---------------------------------------------------------------------------
# Address structure — every hash call gets a unique (domain, position) binding
# to prevent multi-target quantum attacks (same role as SPHINCS+ ADRS).
# ---------------------------------------------------------------------------

def _addr(leaf_idx: int, chain_idx: int, chain_step: int) -> bytes:
    return leaf_idx.to_bytes(4, 'big') + chain_idx.to_bytes(2, 'big') + chain_step.to_bytes(2, 'big')

def _leaf_addr(leaf_idx: int) -> bytes:
    return leaf_idx.to_bytes(4, 'big')

def _node_addr(level: int, index: int) -> bytes:
    return level.to_bytes(2, 'big') + index.to_bytes(4, 'big')

# ---------------------------------------------------------------------------
# Parameters
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Params:
    n: int = 16     # hash output bytes (16 = NIST Level I, matching SPHINCS+-128s)
    w: int = 16     # Winternitz parameter (tradeoff: larger w = smaller sig, slower verify)
    H: int = 20     # tree height (max signatures = 2^H)

    @property
    def lg_w(self) -> int:
        return int(math.log2(self.w))

    @property
    def l1(self) -> int:
        return math.ceil(8 * self.n / self.lg_w)

    @property
    def l2(self) -> int:
        max_csum = self.l1 * (self.w - 1)
        if max_csum == 0:
            return 1
        return math.ceil(math.ceil(math.log2(max_csum + 1)) / self.lg_w)

    @property
    def l(self) -> int:
        return self.l1 + self.l2

    @property
    def max_sigs(self) -> int:
        return 1 << self.H

    @property
    def ots_sig_bytes(self) -> int:
        return self.l * self.n

    @property
    def auth_state_bytes(self) -> int:
        return self.H * self.n + 4


# ---------------------------------------------------------------------------
# Hash primitives
# ---------------------------------------------------------------------------

def hash_n(domain: bytes, seed: bytes, addr: bytes, data: bytes, n: int) -> bytes:
    """Tweaked hash: H(domain || seed || addr || data)[:n].
    The per-key public seed makes each account's hash family independent."""
    return hashlib.sha256(domain + seed + addr + data).digest()[:n]


def prf(sk_seed: bytes, index: bytes, n: int) -> bytes:
    return hmac.new(sk_seed, index, hashlib.sha256).digest()[:n]


# ---------------------------------------------------------------------------
# W-OTS+ (Winternitz One-Time Signature Plus)
# ---------------------------------------------------------------------------

def wots_chain(x: bytes, start: int, steps: int, n: int, seed: bytes,
               leaf_idx: int = 0, chain_idx: int = 0) -> bytes:
    val = x
    for i in range(start, start + steps):
        val = hash_n(DOMAIN_CHAIN, seed, _addr(leaf_idx, chain_idx, i), val, n)
    return val


def base_w(data: bytes, w: int, out_len: int) -> list[int]:
    lg_w = int(math.log2(w))
    digits = []
    buf = 0
    bits = 0
    byte_idx = 0

    for _ in range(out_len):
        while bits < lg_w:
            if byte_idx < len(data):
                buf = (buf << 8) | data[byte_idx]
                byte_idx += 1
            else:
                buf = buf << 8
            bits += 8
        bits -= lg_w
        digits.append((buf >> bits) & (w - 1))

    return digits


def _checksum_bytes(msg_digits: list[int], p: Params) -> bytes:
    csum = sum(p.w - 1 - d for d in msg_digits)
    total_bits = p.l2 * p.lg_w
    total_bytes = math.ceil(total_bits / 8)
    shift = (8 - (total_bits % 8)) % 8
    csum <<= shift
    return csum.to_bytes(total_bytes, 'big')


def _all_digits(msg: bytes, p: Params, seed: bytes) -> list[int]:
    msg_hash = hash_n(DOMAIN_MSG, seed, b'', msg, p.n)
    msg_digits = base_w(msg_hash, p.w, p.l1)
    cs_bytes = _checksum_bytes(msg_digits, p)
    cs_digits = base_w(cs_bytes, p.w, p.l2)
    return msg_digits + cs_digits


def wots_keygen(sk_seed: bytes, pub_seed: bytes, leaf_idx: int,
                p: Params) -> tuple[list[bytes], list[bytes]]:
    sk, pk = [], []
    for chain_idx in range(p.l):
        idx_bytes = leaf_idx.to_bytes(4, 'big') + chain_idx.to_bytes(4, 'big')
        sk_i = prf(sk_seed, idx_bytes, p.n)
        pk_i = wots_chain(sk_i, 0, p.w - 1, p.n, seed=pub_seed,
                          leaf_idx=leaf_idx, chain_idx=chain_idx)
        sk.append(sk_i)
        pk.append(pk_i)
    return sk, pk


def wots_pk_hash(pk_chains: list[bytes], p: Params, pub_seed: bytes,
                 leaf_idx: int = 0) -> bytes:
    return hash_n(DOMAIN_LEAF, pub_seed, _leaf_addr(leaf_idx),
                  b''.join(pk_chains), p.n)


def wots_sign(sk_chains: list[bytes], msg: bytes, p: Params, pub_seed: bytes,
              leaf_idx: int = 0) -> list[bytes]:
    digits = _all_digits(msg, p, pub_seed)
    return [wots_chain(sk_chains[i], 0, d, p.n, seed=pub_seed,
                       leaf_idx=leaf_idx, chain_idx=i)
            for i, d in enumerate(digits)]


def wots_verify(sig_chains: list[bytes], msg: bytes, pk_chains: list[bytes],
                p: Params, pub_seed: bytes, leaf_idx: int = 0) -> bool:
    digits = _all_digits(msg, p, pub_seed)
    for i, d in enumerate(digits):
        if wots_chain(sig_chains[i], d, p.w - 1 - d, p.n, seed=pub_seed,
                      leaf_idx=leaf_idx, chain_idx=i) != pk_chains[i]:
            return False
    return True


def wots_recover_leaf(sig_chains: list[bytes], msg: bytes, p: Params,
                      pub_seed: bytes, leaf_idx: int = 0) -> bytes:
    digits = _all_digits(msg, p, pub_seed)
    recovered_pk = [wots_chain(sig_chains[i], d, p.w - 1 - d, p.n, seed=pub_seed,
                               leaf_idx=leaf_idx, chain_idx=i)
                    for i, d in enumerate(digits)]
    return wots_pk_hash(recovered_pk, p, pub_seed, leaf_idx=leaf_idx)


# ---------------------------------------------------------------------------
# Merkle tree
# ---------------------------------------------------------------------------

def merkle_node_hash(left: bytes, right: bytes, n: int, seed: bytes,
                     level: int = 0, index: int = 0) -> bytes:
    return hash_n(DOMAIN_NODE, seed, _node_addr(level, index), left + right, n)


def build_merkle_tree(leaves: list[bytes], n: int,
                      seed: bytes) -> list[list[bytes]]:
    levels = [leaves]
    current = leaves
    lv = 1
    while len(current) > 1:
        nxt = []
        for i in range(0, len(current), 2):
            nxt.append(merkle_node_hash(current[i], current[i + 1], n, seed,
                                        level=lv, index=i // 2))
        levels.append(nxt)
        current = nxt
        lv += 1
    return levels


def merkle_auth_path(tree: list[list[bytes]], leaf_idx: int) -> list[bytes]:
    path = []
    idx = leaf_idx
    for level in tree[:-1]:
        path.append(level[idx ^ 1])
        idx >>= 1
    return path


def merkle_root_from_leaf(leaf_hash: bytes, leaf_idx: int,
                          auth_path: list[bytes], n: int,
                          seed: bytes) -> bytes:
    cur = leaf_hash
    idx = leaf_idx
    for lv, sibling in enumerate(auth_path):
        parent_idx = idx >> 1
        if idx & 1 == 0:
            cur = merkle_node_hash(cur, sibling, n, seed,
                                   level=lv + 1, index=parent_idx)
        else:
            cur = merkle_node_hash(sibling, cur, n, seed,
                                   level=lv + 1, index=parent_idx)
        idx >>= 1
    return cur


# ---------------------------------------------------------------------------
# Delta computation
# ---------------------------------------------------------------------------

def merge_level(target_index: int) -> int:
    if target_index <= 0:
        return 0
    v = 0
    i = target_index
    while i & 1 == 0:
        v += 1
        i >>= 1
    return v + 1


def delta_count(target_index: int) -> int:
    """Number of NEW sibling hashes the signer must provide for the transition
    to target_index.  The sibling at the highest changed level (M-1) is
    derivable by the verifier from the just-verified leaf, so delta = M - 1."""
    if target_index <= 0:
        return 0
    return merge_level(target_index) - 1


# ---------------------------------------------------------------------------
# Scheme types
# ---------------------------------------------------------------------------

@dataclass
class FullKey:
    seed: bytes       # secret seed (sk in the paper)
    pub_seed: bytes   # public seed (seed in the paper)
    params: Params
    tree: list[list[bytes]]
    root: bytes


@dataclass
class PublicKey:
    root: bytes
    seed: bytes       # public seed
    params: Params


@dataclass
class AuthState:
    next_index: int
    cached_siblings: list[bytes]

    @property
    def size_bytes(self) -> int:
        n = len(self.cached_siblings[0]) if self.cached_siblings else 0
        return 4 + len(self.cached_siblings) * n


@dataclass
class Signature:
    index: int
    ots_sig: list[bytes]
    delta: list[bytes]

    @property
    def size_bytes(self) -> int:
        n = len(self.ots_sig[0]) if self.ots_sig else 0
        return 4 + len(self.ots_sig) * n + len(self.delta) * n


# ---------------------------------------------------------------------------
# Scheme operations
# ---------------------------------------------------------------------------

def keygen(p: Params, seed: Optional[bytes] = None) -> tuple[FullKey, PublicKey]:
    if seed is None:
        seed = os.urandom(32)
    pub_seed = os.urandom(p.n)

    leaves = []
    for i in range(p.max_sigs):
        _, pk_chains = wots_keygen(seed, pub_seed, i, p)
        leaves.append(wots_pk_hash(pk_chains, p, pub_seed, leaf_idx=i))

    tree = build_merkle_tree(leaves, p.n, pub_seed)
    root = tree[-1][0]

    fk = FullKey(seed=seed, pub_seed=pub_seed, params=p, tree=tree, root=root)
    pk = PublicKey(root=root, seed=pub_seed, params=p)
    return fk, pk


def create_account(pk: PublicKey, leaf_0_hash: bytes,
                   auth_path_0: list[bytes]) -> Optional[AuthState]:
    computed_root = merkle_root_from_leaf(leaf_0_hash, 0, auth_path_0,
                                          pk.params.n, pk.seed)
    if computed_root != pk.root:
        return None
    return AuthState(next_index=0, cached_siblings=list(auth_path_0))


def registration_data(fk: FullKey) -> tuple[bytes, list[bytes]]:
    leaf_0_hash = fk.tree[0][0]
    auth_0 = merkle_auth_path(fk.tree, 0)
    return leaf_0_hash, auth_0


def _bound_payload(msg: bytes, delta: list[bytes]) -> bytes:
    """Bind the message and delta into a single payload for OTS signing.
    LE64 length prefix per the paper specification."""
    length = len(msg).to_bytes(8, 'little')
    return length + msg + b''.join(delta)


def sign(fk: FullKey, msg: bytes, index: int) -> Signature:
    p = fk.params
    assert 0 <= index < p.max_sigs

    sk_chains, _ = wots_keygen(fk.seed, fk.pub_seed, index, p)

    target_next = index + 1
    dc = delta_count(target_next) if target_next < p.max_sigs else 0
    delta = []
    for level in range(dc):
        next_at_level = target_next >> level
        sibling_idx = next_at_level ^ 1
        delta.append(fk.tree[level][sibling_idx])

    bound = _bound_payload(msg, delta)
    ots_sig = wots_sign(sk_chains, bound, p, fk.pub_seed, leaf_idx=index)

    return Signature(index=index, ots_sig=ots_sig, delta=delta)


def verify_and_update(pk: PublicKey, msg: bytes, sig: Signature,
                      state: AuthState) -> tuple[bool, Optional[AuthState]]:
    p = pk.params

    if sig.index != state.next_index:
        return False, None
    if sig.index >= p.max_sigs:
        return False, None

    bound = _bound_payload(msg, sig.delta)
    leaf_hash = wots_recover_leaf(sig.ots_sig, bound, p, pk.seed,
                                  leaf_idx=sig.index)

    root = merkle_root_from_leaf(leaf_hash, sig.index, state.cached_siblings,
                                 p.n, pk.seed)
    if root != pk.root:
        return False, None

    next_idx = sig.index + 1
    if next_idx >= p.max_sigs:
        return True, AuthState(next_index=next_idx, cached_siblings=state.cached_siblings)

    new_siblings = list(state.cached_siblings)

    M = merge_level(next_idx)

    node = leaf_hash
    idx = sig.index
    for lv in range(min(M - 1, p.H)):
        sib = state.cached_siblings[lv]
        parent_idx = idx >> 1
        if idx & 1 == 0:
            node = merkle_node_hash(node, sib, p.n, pk.seed,
                                    level=lv + 1, index=parent_idx)
        else:
            node = merkle_node_hash(sib, node, p.n, pk.seed,
                                    level=lv + 1, index=parent_idx)
        idx >>= 1
    if M - 1 < p.H:
        new_siblings[M - 1] = node

    for di in range(len(sig.delta)):
        new_siblings[di] = sig.delta[di]

    return True, AuthState(next_index=next_idx, cached_siblings=new_siblings)
