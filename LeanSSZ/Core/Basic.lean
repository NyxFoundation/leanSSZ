/-
Core SSZ typeclasses and error type.

Layered design:

  - `SSZCodec T`  — the operations, at the `List UInt8` level:
                    `enc : T → List UInt8` and a total, scope-delimited
                    `dec : List UInt8 → Except SSZError T`. Lists (not
                    `ByteArray`) are the proof substrate: sequence and
                    container roundtrips go through by induction with
                    `take` / `drop` / `++` lemmas.
  - `LawfulSSZ T` — the laws: encode/decode roundtrip and the static size
                    bound. Injectivity of `enc` (non-malleability) is NOT
                    a field: it is derived once from the roundtrip law
                    (`enc_injective` below).
  - `SSZFixed T`  — fixed-size types: the exact encoded byte width plus
                    its proof. Sequence and container codecs demand this
                    of their fixed-size element/field types.

The `ByteArray`-facing surface (`serialize` / `deserialize`) is derived
generically at the bottom of this file; production callers use it, proofs
never look below the list level.

SSZ decoding is scope-delimited (each value decodes from exactly the bytes
assigned to it), so `dec` consumes its whole input — there is no remainder.
`dec` is total over all byte strings and strict, so the proven decoder can
serve as the authoritative parser at a C ABI boundary.
-/

namespace LeanSSZ

/-- SSZ decode failures. Mirrors the `SSZError` hierarchy in
`src/lean_spec/spec/ssz/exceptions.py` (collapsed to the cases a pure
decoder can actually hit). -/
inductive SSZError where
  /-- Input length differs from what the type requires. -/
  | invalidLength (expected got : Nat)
  /-- Bytes are structurally well-sized but encode no valid value. -/
  | invalidValue (msg : String)
  /-- An offset table violates monotonicity / bounds. -/
  | invalidOffset (msg : String)
  deriving Repr, DecidableEq

/-- SSZ-encodable types: the operations, over byte lists. -/
class SSZCodec (T : Type) where
  enc : T → List UInt8
  dec : List UInt8 → Except SSZError T
  /-- `true` iff every value of `T` encodes to the same length. -/
  isFixedSize : Bool
  /-- Upper bound on `(enc x).length`; exact for fixed-size types. -/
  maxSize : Nat

export SSZCodec (enc dec)

/-- SSZ-encodable types: the laws. -/
class LawfulSSZ (T : Type) [SSZCodec T] : Prop where
  /-- Roundtrip: decoding an encoding recovers the value. -/
  dec_enc : ∀ x : T, dec (enc x) = .ok x
  /-- Static size bound derived from the schema. -/
  enc_size_le : ∀ x : T, (enc x).length ≤ SSZCodec.maxSize (T := T)

export LawfulSSZ (dec_enc enc_size_le)

/-- Fixed-size SSZ types: the exact width, with proof. -/
class SSZFixed (T : Type) [SSZCodec T] where
  size : Nat
  enc_size : ∀ x : T, (enc x).length = size

/-- Fixed-size element types with positive width. SSZ cannot delimit
zero-width elements inside a sequence, so sequence codecs require this. -/
class SSZPositive (T : Type) [SSZCodec T] [SSZFixed T] : Prop where
  pos : 0 < SSZFixed.size T

/-- Non-malleability: `enc` is injective. Derived from the roundtrip law,
so no per-type proof is ever needed. -/
theorem enc_injective (T : Type) [SSZCodec T] [LawfulSSZ T] :
    ∀ x y : T, enc x = enc y → x = y := by
  intro x y h
  have hx := dec_enc x
  have hy := dec_enc y
  rw [h] at hx
  exact Except.ok.inj (hx.symm.trans hy)

/-! ## ByteArray-facing surface (production callers) -/

/-- Serialize to a `ByteArray`. -/
def serialize {T : Type} [SSZCodec T] (x : T) : ByteArray :=
  ⟨(enc x).toArray⟩

/-- Deserialize from a `ByteArray`. Total and strict. -/
def deserialize {T : Type} [SSZCodec T] (bs : ByteArray) : Except SSZError T :=
  dec bs.data.toList

theorem deserialize_serialize {T : Type} [SSZCodec T] [LawfulSSZ T] (x : T) :
    deserialize (serialize x) = .ok x := by
  simp [deserialize, serialize, dec_enc]

theorem serialize_injective (T : Type) [SSZCodec T] [LawfulSSZ T] :
    ∀ x y : T, serialize x = serialize y → x = y := by
  intro x y h
  apply enc_injective T
  have : (enc x).toArray = (enc y).toArray := congrArg ByteArray.data h
  simpa using congrArg Array.toList this

theorem serialize_size_le {T : Type} [SSZCodec T] [LawfulSSZ T] (x : T) :
    (serialize x).size ≤ SSZCodec.maxSize (T := T) := by
  simpa [serialize, ByteArray.size] using enc_size_le x

end LeanSSZ
