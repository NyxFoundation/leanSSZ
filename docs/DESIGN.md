---
title: leanSSZ Design
last_updated: 2026-07-21
tags:
  - ssz
  - lean4
  - formal-verification
---

# leanSSZ Design

## Scope

leanSSZ implements exactly the SSZ subset used by
[leanSpec](https://github.com/leanEthereum/leanSpec)
(`src/lean_spec/spec/ssz/` + `spec/crypto/merkleization.py`):

| Kind | Types |
|---|---|
| Basic | `Boolean`, `Uint8/16/32/64` (LE) |
| Bytes | `Bytes4/16/20/32/33/52/64` (`BytesN n`), `ByteList` (512 KiB cap) |
| Collections | `SSZVector T n`, `SSZList T limit` |
| Bitfields | `Bitvector n`, `Bitlist limit` |
| Composite | `Container` (fixed and variable fields, 4-byte offsets) |

Deliberately out of scope (leanSpec does not use them): `Uint128/256`,
unions, progressive containers, the mainline `consensus-specs` fork
containers.

## Core abstractions

```lean
class SSZType (T : Type) where
  serialize   : T → ByteArray
  deserialize : ByteArray → Except SSZError T
  isFixedSize : Bool
  maxSize     : Nat

class LawfulSSZ (T : Type) [SSZType T] : Prop where
  decode_encode      : ∀ x, deserialize (serialize x) = .ok x
  encode_size_le_max : ∀ x, (serialize x).size ≤ maxSize
```

Central theorems per type:

1. **Roundtrip** (`decode_encode`) — a `LawfulSSZ` field.
2. **Non-malleability** (`serialize_injective`) — derived *once* from
   roundtrip in `Core/Basic.lean`; never proved per type.
3. **Size bound** (`encode_size_le_max`) — a `LawfulSSZ` field.

`deserialize` is total over all byte strings and strict (exact length /
offset consistency), so the proven Lean decoder is the authoritative
parser at the C ABI boundary (Verity C-8 seam pattern).

## Hashing policy

The hash function is **not** implemented in Lean. SHA-256 comes in via
`@[extern]` FFI with named equivalence axioms, NIST CAVP vectors as the
behavioural check. Collision resistance is an axiom (SSZ-7), following
formal-leanSpec's "crypto primitives are out of scope" rule. A pure-Lean
reference implementation is a possible later addition (kernel-reducible
proofs, FFI-replacement oracle), not a v1 goal. The `Hasher` typeclass is
the future swap point (Poseidon2 / Beam Chain).

Merkleization is v1-uncached; a cached tree is added only if measured
performance demands it (Verity PoC data: STF+HTR 27.5 ms @ V=4096,
within SLO).

## Proposition catalog

SSZ-1 … SSZ-7 are migrated from formal-leanSpec
(`docs/lean4-proof-propositions.md`); new propositions land as SSZ-8+.
formal-leanSpec is intended to eventually depend on this package instead
of its internal `LeanSpec/SSZ/`.

| ID | Statement | Where |
|---|---|---|
| SSZ-1 | Boolean roundtrip | `Core/Boolean.lean` |
| SSZ-2 | Uint64 range | `Core/Uint.lean` |
| SSZ-3 | Uint64 8-byte LE roundtrip | `Core/Uint.lean` |
| SSZ-4 | BytesN length (generalized from Bytes32) | `Core/Bytes.lean` |
| SSZ-5 | SSZVector length | `Core/Vector.lean` |
| SSZ-6 | Power-of-two ceiling minimality | `Core/Utils.lean` |
| SSZ-7 | Hash collision resistance | axiom, with Merkle phase |

## Phases

| Phase | Content | Exit criterion |
|---|---|---|
| 1. Fixed-size core | Boolean / UintN / BytesN / Bitvector / fixed-field containers + 3 theorems | fixed-size fixtures pass |
| 2. Variable-size | SSZList / Bitlist / ByteList / offset containers + 3 theorems | all devnet fixtures pass |
| 3. Merkle + export | merkleization for all types, `@[export]` C ABI layer, minimal Rust caller PoC | Rust-side roundtrip + HTR match |
| 4. Integration | formal-leanSpec switches to leanSSZ dependency | formal-leanSpec builds green |

Phase 2 (variable-size containers under proof) is the part prior art
(SizzLean's `BasicSupported` cut) leaves open; closing it is this
library's distinguishing goal.

## Conformance

leanSpec's SSZ JSON fixtures (`fixtures/consensus/ssz/devnet/ssz/`:
consensus / networking / xmss containers) are vendored under
`Tests/fixtures/` and pinned to a leanSpec commit. Anything excluded from
the run is listed explicitly — no silent scope cuts.

## Trust footprint

See [TRUST.md](TRUST.md). CI greps for `^axiom |^@\[extern` and fails on
any commitment not listed there.
