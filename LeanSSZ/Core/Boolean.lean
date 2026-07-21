/-
SSZ Boolean primitive.

Mirrors `src/lean_spec/spec/ssz/boolean.py` in leanSpec:
  - encode: `True → 0x01`, `False → 0x00` (always 1 byte)
  - decode: accepts only a single byte that is 0x00 or 0x01;
            anything else is a serialization error.

Migrated from formal-leanSpec `LeanSpec/SSZ/Boolean.lean` (discharges SSZ-1
of the proposition catalog).
-/

import LeanSSZ.Core.Basic

namespace LeanSSZ

abbrev Boolean := Bool

namespace Boolean

def encB (b : Boolean) : List UInt8 :=
  [if b then 1 else 0]

def decB : List UInt8 → Except SSZError Boolean
  | [0] => .ok false
  | [1] => .ok true
  | _   => .error (.invalidValue "boolean must be exactly one byte, 0x00 or 0x01")

/-- SSZ-1: a Boolean is recovered by encode/decode. -/
theorem decB_encB (b : Boolean) : decB (encB b) = .ok b := by
  cases b <;> rfl

theorem encB_length (b : Boolean) : (encB b).length = 1 := by
  cases b <;> rfl

end Boolean

instance : SSZCodec Boolean where
  enc := Boolean.encB
  dec := Boolean.decB
  isFixedSize := true
  maxSize := 1

instance : LawfulSSZ Boolean where
  dec_enc := Boolean.decB_encB
  enc_size_le b := Nat.le_of_eq (Boolean.encB_length b)

instance : SSZFixed Boolean where
  size := 1
  enc_size := Boolean.encB_length

instance : SSZPositive Boolean := ⟨Nat.one_pos⟩

end LeanSSZ
