# leanSSZ

A formally verified [SSZ](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md)
library in Lean 4 for the [Lean Ethereum consensus specification](https://github.com/leanEthereum/leanSpec)
(leanSpec), by Nyx Foundation.

leanSSZ targets **leanSpec's SSZ subset only** — not the mainline
`consensus-specs` type universe. The type set is deliberately small
(`Uint8/16/32/64`, `Boolean`, `BytesN`, `SSZVector`, `SSZList`,
`Bitvector`, `Bitlist`, `Container`; no `Uint128/256`, no progressive
containers), and the goal is **100% proof coverage over that subset**:
every type ships with machine-checked roundtrip, non-malleability, and
static size-bound theorems.

## Design

- Two-layer typeclasses: `SSZType` (operations) / `LawfulSSZ` (laws),
  mirroring the `BEq` / `LawfulBEq` idiom. Injectivity of `serialize` is
  derived once from the roundtrip law — never proved per type.
- `deserialize` is total (`Except SSZError`) and strict, so the proven
  decoder can serve as the authoritative parser at a C ABI boundary.
- Trust footprint is grep-able:
  `grep -rEn '^axiom |^@\[extern' LeanSSZ/` lists every trust commitment.
- SSZ modules originate from
  [NyxFoundation/formal-leanSpec](https://github.com/NyxFoundation/formal-leanSpec)'s
  proposition catalog (SSZ-1 … SSZ-7) and are extended here; leanSSZ is
  intended to become that model's SSZ dependency.

See [docs/DESIGN.md](docs/DESIGN.md) for the full design and roadmap, and
[docs/TRUST.md](docs/TRUST.md) for the trust footprint.

## Build

```bash
lake build   # builds the library and checks every proof
```

The toolchain is pinned by `lean-toolchain` (matches formal-leanSpec).

## Status

Phases 1–3 complete:

- **Core codecs, proven**: `Boolean`, `Uint8/16/32/64`, `BytesN`,
  `SSZVector`, `SSZList` (packed and offset-table layouts), `Bitvector`,
  `Bitlist`, containers (fixed and variable fields) — every codec ships
  machine-checked roundtrip, injectivity (derived once), and size-bound
  theorems. The serialization core is axiom-free over the kernel.
- **Merkleization**: `hash_tree_root` for all types, SHA-256 via C FFI
  (the library's only trust commitments — see `docs/TRUST.md`),
  validated by NIST known answers (`lake exe sanity`).
- **Conformance**: all 34 leanSpec devnet SSZ fixtures pass
  (`lake exe fixtures`; fixtures vendored, pinned to leanSpec
  `4c9d640d`). Fixtures carry no `hash_tree_root`, so root computation
  is covered by known answers only.
- **C ABI + Rust PoC**: `LeanSSZ/Export.lean` exposes
  validate / re-encode / hash_tree_root for `Block` over bytes-only
  functions; `poc/rust-caller` links the Lean static library and passes
  roundtrip, root, and malformed-input rejection checks end to end.

Known scope notes: XMSS `Signature` is modeled as an opaque fixed
424-byte blob (matches the wire format; its container-structured
`hash_tree_root` is not modeled). Devnet limits are pinned as type
parameters.
