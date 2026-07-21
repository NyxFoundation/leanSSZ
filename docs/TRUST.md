---
title: leanSSZ Trust Footprint
last_updated: 2026-07-21
tags:
  - trust
  - formal-verification
---

# leanSSZ Trust Footprint

Everything the proofs rely on beyond the Lean kernel's standard axioms.
Recover the in-repo inventory at any time with:

```bash
grep -rEn '^axiom |^@\[extern' LeanSSZ/ --include='*.lean'
```

## Outside the repository (accepted TCB)

- **Lean 4 kernel** — proof checking.
- **Lean C backend** — compiles the proven functions faithfully. Proofs
  are design-time artifacts; consumers call the compiled pure functions
  (e.g. over a C ABI) without re-verification.

## Inside the repository

| Commitment | Kind | Location | Notes |
|---|---|---|---|
| `Sha256.combineRaw` | `@[extern "lssz_sha256_combine"]` | `LeanSSZ/Hasher/Sha256FFI.lean` | hash of two 32-byte inputs; the sole merkleization primitive |
| `Sha256.hashRaw` | `@[extern "lssz_sha256"]` | `LeanSSZ/Hasher/Sha256FFI.lean` | general SHA-256, exposed for CAVP validation only |
| `Sha256.combineRaw_size` | `axiom` | `LeanSSZ/Hasher/Sha256FFI.lean` | FFI combine returns 32 bytes; replaceable by a theorem once a pure implementation lands |
| `HasHTR.collisionResistance` | `axiom` (SSZ-7) | `LeanSSZ/Merkle/Root.lean` | idealized injectivity of the SHA-256 merkleization; cryptographic assumption, not provable |

The C implementation itself (`c/sha256.c`) is outside the proof boundary;
`lake exe sanity` checks it against NIST known answers and the Ethereum
zero-subtree roots.

The serialization core (`LeanSSZ/Core/`) — every roundtrip, injectivity,
and size-bound theorem — is axiom-free over the kernel: the commitments
above are reachable only from `hash_tree_root`.

Rules:

1. New `axiom` / `@[extern]` declarations are allowed **only** under
   `LeanSSZ/Hasher/` (plus SSZ-7 alongside the Merkle root typeclass).
2. Every addition must be listed in the table above in the same commit.
3. CI fails if the grep output and this document disagree.
