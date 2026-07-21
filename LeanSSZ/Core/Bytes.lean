/-
SSZ fixed-length byte sequences.

Mirrors `src/lean_spec/spec/ssz/byte_arrays.py` in leanSpec: `BaseBytes`
subclasses of widths 4, 16, 20, 32, 33, 52, 64. A `BytesN n` value carries
its length invariant in the type (a subtype over `ByteArray`), so the
length lemma is by construction — no runtime re-checks.

`Bytes32` discharges SSZ-4 of the proposition catalog (migrated from
formal-leanSpec `LeanSpec/SSZ/Bytes32.lean`, generalized over the width).
-/

import LeanSSZ.Core.Basic

namespace LeanSSZ

/-- Fixed-length byte sequence: a `ByteArray` whose size is pinned to `n`
by the type. -/
def BytesN (n : Nat) := { b : ByteArray // b.size = n }

abbrev Bytes4  := BytesN 4
abbrev Bytes16 := BytesN 16
abbrev Bytes20 := BytesN 20
abbrev Bytes32 := BytesN 32
abbrev Bytes33 := BytesN 33
abbrev Bytes52 := BytesN 52
abbrev Bytes64 := BytesN 64

namespace BytesN

variable {n : Nat}

@[inline] def size (b : BytesN n) : Nat := b.val.size

/-- SSZ-4 (generalized): a `BytesN n` is always `n` bytes. -/
theorem size_eq (b : BytesN n) : b.size = n := b.property

def zero (n : Nat) : BytesN n := ⟨⟨Array.replicate n 0⟩, by simp [ByteArray.size]⟩

instance : Inhabited (BytesN n) := ⟨zero n⟩

instance : BEq (BytesN n) := ⟨fun a b => a.val.data == b.val.data⟩

instance : LawfulBEq (BytesN n) where
  eq_of_beq {a b} h := by
    obtain ⟨⟨da⟩, ha⟩ := a
    obtain ⟨⟨db⟩, hb⟩ := b
    have : da = db := eq_of_beq h
    subst this
    rfl
  rfl {a} := by
    show a.val.data == a.val.data
    exact beq_self_eq_true a.val.data

instance : Repr (BytesN n) := ⟨fun b p => reprPrec b.val.data p⟩

/-- Serialization is the identity on the underlying bytes. -/
def encB (b : BytesN n) : List UInt8 := b.val.data.toList

def decB (bs : List UInt8) : Except SSZError (BytesN n) :=
  if h : bs.length = n then
    .ok ⟨⟨bs.toArray⟩, by simpa [ByteArray.size] using h⟩
  else
    .error (.invalidLength n bs.length)

theorem encB_length (b : BytesN n) : (encB b).length = n := by
  simpa [encB] using b.property

theorem decB_encB (b : BytesN n) : decB (encB b) = .ok b := by
  obtain ⟨⟨d⟩, h⟩ := b
  have hd : d.size = n := by simpa [ByteArray.size] using h
  simp [decB, encB, hd]

end BytesN

instance {n : Nat} : SSZCodec (BytesN n) where
  enc := BytesN.encB
  dec := BytesN.decB
  isFixedSize := true
  maxSize := n

instance {n : Nat} : LawfulSSZ (BytesN n) where
  dec_enc := BytesN.decB_encB
  enc_size_le b := Nat.le_of_eq (BytesN.encB_length b)

instance {n : Nat} : SSZFixed (BytesN n) where
  size := n
  enc_size := BytesN.encB_length

/-- Positivity per concrete width (all widths leanSpec uses). Stated on
`BytesN <literal>` so instance search needs no arithmetic. -/
instance : SSZPositive (BytesN 4)  := ⟨by decide⟩
instance : SSZPositive (BytesN 16) := ⟨by decide⟩
instance : SSZPositive (BytesN 20) := ⟨by decide⟩
instance : SSZPositive (BytesN 32) := ⟨by decide⟩
instance : SSZPositive (BytesN 33) := ⟨by decide⟩
instance : SSZPositive (BytesN 52) := ⟨by decide⟩
instance : SSZPositive (BytesN 64) := ⟨by decide⟩

end LeanSSZ
