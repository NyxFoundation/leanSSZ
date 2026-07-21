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

Phase 1 (fixed-size core) in progress. Conformance target: the SSZ JSON
fixtures shipped with leanSpec (`fixtures/consensus/ssz/`).
