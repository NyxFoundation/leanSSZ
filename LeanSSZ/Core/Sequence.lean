/-
Shared machinery for homogeneous SSZ sequences of FIXED-size elements.

Mirrors the fixed-size arm of `src/lean_spec/spec/ssz/collections.py`:
element bodies pack back-to-back with no separator; the decoder cuts the
input into `size`-wide chunks and decodes each.

The roundtrip proof is a single induction over the element list, using the
`SSZFixed` width to align `take` / `drop` with encoding boundaries. Both
`SSZVector` (exact count) and `SSZList` (count inferred from scope, capped
by the limit) reduce to this machinery.
-/

import LeanSSZ.Core.Basic
import LeanSSZ.Core.Vector

namespace LeanSSZ

namespace Seq

variable {T : Type} [SSZCodec T]

/-- Concatenate the element encodings, no separators. -/
def encSeq (xs : List T) : List UInt8 := xs.flatMap enc

/-- Decode exactly `count` elements of width `width` from `bs`,
consuming the whole input. -/
def decSeq (width : Nat) : Nat → List UInt8 → Except SSZError (List T)
  | 0, [] => .ok []
  | 0, rest => .error (.invalidLength 0 rest.length)
  | count + 1, bs => do
    let x ← dec (bs.take width)
    let xs ← decSeq width count (bs.drop width)
    pure (x :: xs)

private theorem take_len_append (as bs : List UInt8) :
    (as ++ bs).take as.length = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem drop_len_append (as bs : List UInt8) :
    (as ++ bs).drop as.length = bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem encSeq_length [SSZFixed T] (xs : List T) :
    (encSeq xs).length = xs.length * SSZFixed.size T := by
  induction xs with
  | nil => simp [encSeq]
  | cons x xs ih =>
    simp only [encSeq, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [encSeq] at ih
    rw [SSZFixed.enc_size x, ih, Nat.succ_mul, Nat.add_comm]

/-- Sequence roundtrip: `count` and the byte widths line up, every element
decodes back. -/
theorem decSeq_encSeq [LawfulSSZ T] [SSZFixed T] (xs : List T) :
    decSeq (SSZFixed.size T) xs.length (encSeq xs) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show decSeq (SSZFixed.size T) (xs.length + 1) (enc x ++ encSeq xs) = .ok (x :: xs)
    unfold decSeq
    rw [← SSZFixed.enc_size (T := T) x, take_len_append, drop_len_append,
        SSZFixed.enc_size (T := T) x]
    rw [dec_enc x]
    show (do
      let xs' ← decSeq (SSZFixed.size T) xs.length (encSeq xs)
      pure (x :: xs') : Except SSZError (List T)) = .ok (x :: xs)
    rw [ih]
    rfl

end Seq

/-! ## SSZVector of fixed-size elements -/

namespace SSZVector

variable {T : Type} {n : Nat} [SSZCodec T] [SSZFixed T]

def encV (v : SSZVector T n) : List UInt8 := Seq.encSeq v.data.toList

def decV (bs : List UInt8) : Except SSZError (SSZVector T n) :=
  if bs.length = n * SSZFixed.size T then
    match Seq.decSeq (T := T) (SSZFixed.size T) n bs with
    | .error e => .error e
    | .ok xs =>
      if h : xs.length = n then
        .ok ⟨xs.toArray, by simpa using h⟩
      else
        .error (.invalidValue "internal: element count mismatch")
  else
    .error (.invalidLength (n * SSZFixed.size T) bs.length)

theorem encV_length (v : SSZVector T n) :
    (encV v).length = n * SSZFixed.size T := by
  unfold encV
  rw [Seq.encSeq_length, Array.length_toList, v.size_eq]

theorem decV_encV [LawfulSSZ T] (v : SSZVector T n) : decV (encV v) = .ok v := by
  obtain ⟨data, size_eq⟩ := v
  have hlen : data.toList.length = n := by
    rw [Array.length_toList, size_eq]
  have hround := Seq.decSeq_encSeq (T := T) data.toList
  rw [hlen] at hround
  unfold decV encV
  rw [if_pos (by rw [Seq.encSeq_length, Array.length_toList, size_eq])]
  simp only [hround, dif_pos hlen]

end SSZVector

instance {T : Type} {n : Nat} [SSZCodec T] [SSZFixed T] : SSZCodec (SSZVector T n) where
  enc := SSZVector.encV
  dec := SSZVector.decV
  isFixedSize := true
  maxSize := n * SSZFixed.size T

instance {T : Type} {n : Nat} [SSZCodec T] [SSZFixed T] [LawfulSSZ T] :
    LawfulSSZ (SSZVector T n) where
  dec_enc := SSZVector.decV_encV
  enc_size_le v := Nat.le_of_eq (SSZVector.encV_length v)

instance {T : Type} {n : Nat} [SSZCodec T] [SSZFixed T] : SSZFixed (SSZVector T n) where
  size := n * SSZFixed.size T
  enc_size := SSZVector.encV_length

end LeanSSZ
