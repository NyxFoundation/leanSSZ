/-
Core SSZ typeclasses and error type.

Two-layer design (mirrors the `BEq` / `LawfulBEq` idiom):
  - `SSZType T`   — the operations: serialize / deserialize / size metadata.
  - `LawfulSSZ T` — the laws: encode/decode roundtrip and the static size
                    bound. Injectivity of `serialize` (non-malleability) is
                    NOT a field: it is derived once from the roundtrip law
                    (`serialize_injective` below).

Deserialization is total over all byte strings (`Except`), so a proven
`deserialize` can serve as the authoritative parser at the C ABI boundary.
-/

namespace LeanSSZ

/-- SSZ decode failures. Mirrors `SSZError` hierarchy in
`src/lean_spec/spec/ssz/exceptions.py` (collapsed to the cases a pure
decoder can actually hit). -/
inductive SSZError where
  /-- Input length differs from what the type requires. -/
  | invalidLength (expected got : Nat)
  /-- Bytes are structurally well-sized but encode no valid value. -/
  | invalidValue (msg : String)
  deriving Repr, DecidableEq

/-- SSZ-encodable types: the operations. -/
class SSZType (T : Type) where
  serialize : T → ByteArray
  deserialize : ByteArray → Except SSZError T
  /-- `true` iff every value of `T` serializes to the same length. -/
  isFixedSize : Bool
  /-- Upper bound on `(serialize x).size`; exact for fixed-size types. -/
  maxSize : Nat

/-- SSZ-encodable types: the laws. -/
class LawfulSSZ (T : Type) [SSZType T] : Prop where
  /-- Roundtrip: decoding an encoding recovers the value. -/
  decode_encode : ∀ x : T, SSZType.deserialize (SSZType.serialize x) = .ok x
  /-- Static size bound derived from the schema. -/
  encode_size_le_max : ∀ x : T, (SSZType.serialize x).size ≤ SSZType.maxSize (T := T)

/-- Non-malleability: `serialize` is injective. Derived from the roundtrip
law, so no per-type proof is ever needed. -/
theorem serialize_injective (T : Type) [SSZType T] [LawfulSSZ T] :
    ∀ x y : T, SSZType.serialize x = SSZType.serialize y → x = y := by
  intro x y h
  have hx := LawfulSSZ.decode_encode x
  have hy := LawfulSSZ.decode_encode y
  rw [h] at hx
  exact Except.ok.inj (hx.symm.trans hy)

end LeanSSZ
