/-
SSZ variable-length List of FIXED-size elements.

Mirrors the fixed-size arm of `SSZList` in
`src/lean_spec/spec/ssz/collections.py`: element bodies pack back-to-back;
the decoder infers the element count from the byte budget (`scope / width`,
which must divide exactly) and enforces the limit.

The offset-table arm (variable-size elements) lands with the container
machinery in `Core/Offsets.lean`.

`ByteList` is `SSZList Uint8` — a byte's encoding is itself, so the list
codec specializes to the identity on bytes.
-/

import LeanSSZ.Core.Sequence
import LeanSSZ.Core.Uint

namespace LeanSSZ

/-- A variable-length SSZ list holding at most `limit` elements. -/
structure SSZList (T : Type) (limit : Nat) where
  data : List T
  le_limit : data.length ≤ limit

/-- leanSpec's `ByteList512KiB` bound, in bytes. -/
abbrev ByteList (limit : Nat) := SSZList Uint8 limit
abbrev ByteList512KiB := ByteList (512 * 1024)

namespace SSZList

variable {T : Type} {limit : Nat} [SSZCodec T] [SSZFixed T]

instance : Inhabited (SSZList T limit) := ⟨⟨[], Nat.zero_le _⟩⟩

@[inline] def length (l : SSZList T limit) : Nat := l.data.length

def encL (l : SSZList T limit) : List UInt8 := Seq.encSeq l.data

def decL (bs : List UInt8) : Except SSZError (SSZList T limit) :=
  if bs.length % SSZFixed.size T = 0 ∧ bs.length / SSZFixed.size T ≤ limit then
    match Seq.decSeq (T := T) (SSZFixed.size T) (bs.length / SSZFixed.size T) bs with
    | .error e => .error e
    | .ok xs =>
      if h : xs.length ≤ limit then
        .ok ⟨xs, h⟩
      else
        .error (.invalidValue "internal: element count mismatch")
  else
    .error (.invalidValue "list scope not divisible by element width or over limit")

theorem encL_length (l : SSZList T limit) :
    (encL l).length = l.data.length * SSZFixed.size T :=
  Seq.encSeq_length l.data

theorem encL_length_le (l : SSZList T limit) :
    (encL l).length ≤ limit * SSZFixed.size T := by
  rw [encL_length]
  exact Nat.mul_le_mul_right _ l.le_limit

theorem decL_encL [LawfulSSZ T] [SSZPositive T] (l : SSZList T limit) :
    decL (encL l) = .ok l := by
  obtain ⟨xs, hle⟩ := l
  have hs : 0 < SSZFixed.size T := SSZPositive.pos
  have hlen : (Seq.encSeq (T := T) xs).length = xs.length * SSZFixed.size T :=
    Seq.encSeq_length xs
  have hdiv : (Seq.encSeq (T := T) xs).length / SSZFixed.size T = xs.length := by
    rw [hlen]
    exact Nat.mul_div_cancel _ hs
  unfold decL encL
  rw [if_pos ⟨by rw [hlen]; exact Nat.mul_mod_left .., by rw [hdiv]; exact hle⟩]
  simp only [hdiv, Seq.decSeq_encSeq, dif_pos hle]

end SSZList

instance {T : Type} {limit : Nat} [SSZCodec T] [SSZFixed T] : SSZCodec (SSZList T limit) where
  enc := SSZList.encL
  dec := SSZList.decL
  isFixedSize := false
  maxSize := limit * SSZFixed.size T

instance {T : Type} {limit : Nat} [SSZCodec T] [SSZFixed T] [LawfulSSZ T] [SSZPositive T] :
    LawfulSSZ (SSZList T limit) where
  dec_enc := SSZList.decL_encL
  enc_size_le := SSZList.encL_length_le

end LeanSSZ
