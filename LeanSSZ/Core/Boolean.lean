/-
SSZ Boolean primitive.

Mirrors `src/lean_spec/spec/ssz/boolean.py` in leanSpec:
  - `encode_bytes`: `True → 0x01`, `False → 0x00` (always 1 byte)
  - `decode_bytes`: accepts only a single byte that is 0x00 or 0x01;
                    anything else is a serialization error.

Migrated from formal-leanSpec `LeanSpec/SSZ/Boolean.lean` (discharges SSZ-1
of the proposition catalog) and extended with `SSZType` / `LawfulSSZ`
instances.
-/

import LeanSSZ.Core.Basic

namespace LeanSSZ

abbrev Boolean := Bool

namespace Boolean

def encode (b : Boolean) : ByteArray :=
  ByteArray.mk #[if b then 1 else 0]

def decode (bs : ByteArray) : Except SSZError Boolean :=
  match bs.data with
  | ⟨[0]⟩ => .ok false
  | ⟨[1]⟩ => .ok true
  | _     => .error (.invalidValue "boolean must be exactly one byte, 0x00 or 0x01")

/-- SSZ-1: a Boolean is recovered by encode/decode. -/
theorem decode_encode (b : Boolean) :
    decode (encode b) = .ok b := by
  cases b <;> rfl

theorem encode_size (b : Boolean) : (encode b).size = 1 := by
  cases b <;> rfl

end Boolean

instance : SSZType Boolean where
  serialize := Boolean.encode
  deserialize := Boolean.decode
  isFixedSize := true
  maxSize := 1

instance : LawfulSSZ Boolean where
  decode_encode b := Boolean.decode_encode b
  encode_size_le_max b := Nat.le_of_eq (Boolean.encode_size b)

end LeanSSZ
