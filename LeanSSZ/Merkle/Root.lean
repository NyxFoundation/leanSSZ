/-
`hash_tree_root` instances for every leanSpec SSZ type.

Mirrors the `hash_tree_root` singledispatch table in
`src/lean_spec/spec/crypto/merkleization.py`:
  - basic leaves (uints, booleans) and `BytesN`: pack serialized bytes
    into chunks, merkleize;
  - bitfields: pack bits (NO delimiter), merkleize at the bit-capacity
    chunk limit; bitlists mix in the bit count;
  - vectors/lists of basic elements: pack the concatenated serialization;
    of composite elements: one leaf per element root; lists mix in the
    element count;
  - containers: one leaf per field root (per-container instances).

Carries SSZ-7 (collision resistance) from formal-leanSpec's catalog as an
axiom — a cryptographic assumption, not provable. It is meaningful only
for instances that model the real hash; do not instantiate `HasHTR` with
degenerate (non-injective) roots or the axiom becomes inconsistent.
-/

import LeanSSZ.Core.Sequence
import LeanSSZ.Core.Boolean
import LeanSSZ.Core.List
import LeanSSZ.Core.Bitfields
import LeanSSZ.Merkle.Merkleize

namespace LeanSSZ

/-- Types with an SSZ Merkle root (models the per-type
`hash_tree_root.register` handlers of the Python spec). -/
class HasHTR (T : Type) where
  htr : T → Bytes32

export HasHTR (htr)

/--
SSZ-7: distinct values produce distinct hash-tree roots.

A cryptographic assumption (idealized injectivity of the SHA-256
merkleization), consumed at call sites — not provable. Migrated from
formal-leanSpec `LeanSpec/SSZ/Hash.lean`.
-/
axiom HasHTR.collisionResistance {T : Type} [HasHTR T] :
    ∀ x y : T, htr x = htr y → x = y

/-- Marker for SSZ "basic" types (uints, booleans): their sequences pack
serialized bytes instead of hashing each element. -/
class SSZBasic (T : Type) : Prop

instance : SSZBasic Boolean := ⟨⟩
instance : SSZBasic Uint8 := ⟨⟩
instance : SSZBasic Uint16 := ⟨⟩
instance : SSZBasic Uint32 := ⟨⟩
instance : SSZBasic Uint64 := ⟨⟩

open Merkle

/-! ## Leaves -/

instance [Hasher] : HasHTR Boolean :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

instance [Hasher] : HasHTR Uint8 :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

instance [Hasher] : HasHTR Uint16 :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

instance [Hasher] : HasHTR Uint32 :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

instance [Hasher] : HasHTR Uint64 :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

instance {n : Nat} [Hasher] : HasHTR (BytesN n) :=
  ⟨fun x => merkleize (chunkify (enc x)) none⟩

/-! ## Bitfields -/

instance {n : Nat} [Hasher] : HasHTR (Bitvector n) :=
  ⟨fun v => merkleize
    (chunkify (Bits.packedBytes v.data))
    (some ((n + 255) / 256))⟩

instance {limit : Nat} [Hasher] : HasHTR (Bitlist limit) :=
  ⟨fun l => mixInLength
    (merkleize
      (chunkify (Bits.packedBytes l.data))
      (some ((limit + 255) / 256)))
    l.data.length⟩

/-! ## Sequences -/

/-- Vector of basic elements: pack the concatenated serialization. -/
instance (priority := 1000) instHTRVectorBasic
    {T : Type} {n : Nat} [Hasher] [SSZCodec T] [SSZFixed T] [SSZBasic T] :
    HasHTR (SSZVector T n) :=
  ⟨fun v => merkleize (chunkify (Seq.encSeq v.data.toList))
    (some ((n * SSZFixed.size T + 31) / 32))⟩

/-- Vector of composite elements: one leaf per element root. -/
instance (priority := 500) instHTRVectorComposite
    {T : Type} {n : Nat} [Hasher] [HasHTR T] :
    HasHTR (SSZVector T n) :=
  ⟨fun v => merkleize (v.data.toList.map htr) (some n)⟩

/-- List of basic elements: pack, merkleize at capacity, mix in length. -/
instance (priority := 1000) instHTRListBasic
    {T : Type} {limit : Nat} [Hasher] [SSZCodec T] [SSZFixed T] [SSZBasic T] :
    HasHTR (SSZList T limit) :=
  ⟨fun l => mixInLength
    (merkleize (chunkify (Seq.encSeq l.data))
      (some ((limit * SSZFixed.size T + 31) / 32)))
    l.data.length⟩

/-- List of composite elements: one leaf per element root, mix in length. -/
instance (priority := 500) instHTRListComposite
    {T : Type} {limit : Nat} [Hasher] [HasHTR T] :
    HasHTR (SSZList T limit) :=
  ⟨fun l => mixInLength (merkleize (l.data.map htr) (some limit)) l.data.length⟩

end LeanSSZ
