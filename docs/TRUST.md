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

| Commitment | Kind | Location | Status |
|---|---|---|---|
| *(none yet)* | | | Phase 1 core is axiom-free over the kernel |

Planned commitments (land with the Merkle phase, and nowhere else):

- `sha256Hash` / `sha256Combine` — `@[extern]` FFI primitives,
  `LeanSSZ/Hasher/Sha256FFI.lean` only.
- `sha256*_eq_spec` — equivalence axioms for the FFI primitives
  (each replaceable later by a proved theorem without changing
  dependent statements).
- `collisionResistance` (SSZ-7) — idealized injectivity of the SSZ
  Merkleization; a cryptographic assumption, not provable.

Rules:

1. New `axiom` / `@[extern]` declarations are allowed **only** under
   `LeanSSZ/Hasher/` (plus SSZ-7 alongside the Merkle root typeclass).
2. Every addition must be listed in the table above in the same commit.
3. CI fails if the grep output and this document disagree.
