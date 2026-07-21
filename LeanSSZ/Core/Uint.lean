/-
SSZ unsigned-integer primitives: Uint8 / Uint16 / Uint32 / Uint64.

Mirrors `src/lean_spec/spec/ssz/uint.py` in leanSpec: fixed-width
little-endian byte encoding, decode requires the exact byte count.
leanSpec deliberately has no Uint128/Uint256 — neither do we.

The little-endian positional machinery (`encodeNat` / `decodeNat` and the
digit-peeling lemmas) is shared across widths; it is migrated from
formal-leanSpec `LeanSpec/SSZ/Uint64.lean` (discharges SSZ-2 / SSZ-3 of the
proposition catalog).
-/

import LeanSSZ.Core.Basic

namespace LeanSSZ

/-! ## Shared little-endian machinery -/

namespace LE

/-- `encodeNat n k` writes `n` as `k` little-endian bytes (least-significant first). -/
def encodeNat (n : Nat) : Nat → List UInt8
  | 0     => []
  | k + 1 => UInt8.ofNat (n % 256) :: encodeNat (n / 256) k

/-- `decodeNat bs` reads a little-endian byte list as a natural number. -/
def decodeNat : List UInt8 → Nat
  | []      => 0
  | b :: bs => b.toNat + 256 * decodeNat bs

theorem encodeNat_length (n k : Nat) : (encodeNat n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encodeNat, ih]

theorem decodeNat_lt (bs : List UInt8) : decodeNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [decodeNat]
  | cons b rest ih =>
    show b.toNat + 256 * decodeNat rest < 256 ^ (rest.length + 1)
    have hb : b.toNat < 256 := b.toNat_lt
    have := ih
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ rest.length) 256]
    omega

/--
Positional base-`b` step lemma: peel off the lowest base-`b` digit of `n`,
modulo the next `m` digits.
-/
private theorem mod_step (b n m : Nat) :
    n % (b * m) = n % b + b * ((n / b) % m) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.mul_zero, Nat.mod_zero]
    rw [Nat.add_comm]
    exact (Nat.div_add_mod n b).symm
  have hr_lt : n % b < b := Nat.mod_lt n hb
  have hqm : (n / b) % m < m := Nat.mod_lt _ hm
  have hr_lt_M : n % b < b * m := by
    have : b ≤ b * m := Nat.le_mul_of_pos_right b hm
    omega
  have hbound : b * ((n / b) % m) + n % b < b * m := by
    have h_step : b * ((n / b) % m) + b ≤ b * m := by
      calc b * ((n / b) % m) + b
          = b * ((n / b) % m + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ b * m := Nat.mul_le_mul_left b hqm
    omega
  have h_lhs : n % (b * m) = (b * (n / b) + n % b) % (b * m) := by
    conv =>
      lhs
      rw [← Nat.div_add_mod n b]
  rw [h_lhs]
  calc (b * (n / b) + n % b) % (b * m)
      = ((b * (n / b)) % (b * m) + (n % b) % (b * m)) % (b * m) :=
          Nat.add_mod _ _ _
    _ = (b * ((n / b) % m) + (n % b) % (b * m)) % (b * m) := by
          rw [Nat.mul_mod_mul_left]
    _ = (b * ((n / b) % m) + n % b) % (b * m) := by
          rw [Nat.mod_eq_of_lt hr_lt_M]
    _ = b * ((n / b) % m) + n % b := Nat.mod_eq_of_lt hbound
    _ = n % b + b * ((n / b) % m) := Nat.add_comm _ _

theorem decodeNat_encodeNat (n k : Nat) :
    decodeNat (encodeNat n k) = n % 256 ^ k := by
  induction k generalizing n with
  | zero =>
    show decodeNat [] = n % 1
    simp [decodeNat, Nat.mod_one]
  | succ k ih =>
    show (UInt8.ofNat (n % 256)).toNat + 256 * decodeNat (encodeNat (n / 256) k)
        = n % 256 ^ (k + 1)
    rw [ih]
    have h_uint8 : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
      UInt8.toNat_ofNat_of_lt' (Nat.mod_lt n (by decide))
    rw [h_uint8, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, mod_step]

end LE

/-! ## Width-specific wrappers

Each width `w ∈ {8, 16, 32, 64}` gets `encU` (exactly `w / 8` LE bytes),
`decU` (rejects any other length), the roundtrip theorem, and codec
instances. The bodies are deliberately identical modulo the width; a macro
would obscure more than it saves at four sites.
-/

abbrev Uint8 := UInt8
abbrev Uint16 := UInt16
abbrev Uint32 := UInt32
abbrev Uint64 := UInt64

namespace Uint8

def encU (v : Uint8) : List UInt8 := LE.encodeNat v.toNat 1

def decU (bs : List UInt8) : Except SSZError Uint8 :=
  if bs.length = 1 then
    .ok (UInt8.ofNat (LE.decodeNat bs))
  else
    .error (.invalidLength 1 bs.length)

theorem encU_length (v : Uint8) : (encU v).length = 1 :=
  LE.encodeNat_length ..

theorem decU_encU (v : Uint8) : decU (encU v) = .ok v := by
  unfold decU
  rw [if_pos (encU_length v)]
  congr 1
  show UInt8.ofNat (LE.decodeNat (LE.encodeNat v.toNat 1)) = v
  rw [LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 1 = 2 ^ 8 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt8.ofNat_toNat

end Uint8

namespace Uint16

def encU (v : Uint16) : List UInt8 := LE.encodeNat v.toNat 2

def decU (bs : List UInt8) : Except SSZError Uint16 :=
  if bs.length = 2 then
    .ok (UInt16.ofNat (LE.decodeNat bs))
  else
    .error (.invalidLength 2 bs.length)

theorem encU_length (v : Uint16) : (encU v).length = 2 :=
  LE.encodeNat_length ..

theorem decU_encU (v : Uint16) : decU (encU v) = .ok v := by
  unfold decU
  rw [if_pos (encU_length v)]
  congr 1
  show UInt16.ofNat (LE.decodeNat (LE.encodeNat v.toNat 2)) = v
  rw [LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt16.ofNat_toNat

end Uint16

namespace Uint32

def encU (v : Uint32) : List UInt8 := LE.encodeNat v.toNat 4

def decU (bs : List UInt8) : Except SSZError Uint32 :=
  if bs.length = 4 then
    .ok (UInt32.ofNat (LE.decodeNat bs))
  else
    .error (.invalidLength 4 bs.length)

theorem encU_length (v : Uint32) : (encU v).length = 4 :=
  LE.encodeNat_length ..

theorem decU_encU (v : Uint32) : decU (encU v) = .ok v := by
  unfold decU
  rw [if_pos (encU_length v)]
  congr 1
  show UInt32.ofNat (LE.decodeNat (LE.encodeNat v.toNat 4)) = v
  rw [LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt32.ofNat_toNat

end Uint32

namespace Uint64

/-- SSZ-2: a Uint64 value lies in [0, 2^64). -/
theorem range (v : Uint64) : v.toNat < 2 ^ 64 :=
  v.toNat_lt

def encU (v : Uint64) : List UInt8 := LE.encodeNat v.toNat 8

def decU (bs : List UInt8) : Except SSZError Uint64 :=
  if bs.length = 8 then
    .ok (UInt64.ofNat (LE.decodeNat bs))
  else
    .error (.invalidLength 8 bs.length)

theorem encU_length (v : Uint64) : (encU v).length = 8 :=
  LE.encodeNat_length ..

/-- SSZ-3: a Uint64 is recovered by 8-byte LE encode/decode. -/
theorem decU_encU (v : Uint64) : decU (encU v) = .ok v := by
  unfold decU
  rw [if_pos (encU_length v)]
  congr 1
  show UInt64.ofNat (LE.decodeNat (LE.encodeNat v.toNat 8)) = v
  rw [LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt64.ofNat_toNat

end Uint64

instance : SSZCodec Uint8 where
  enc := Uint8.encU
  dec := Uint8.decU
  isFixedSize := true
  maxSize := 1

instance : LawfulSSZ Uint8 where
  dec_enc := Uint8.decU_encU
  enc_size_le v := Nat.le_of_eq (Uint8.encU_length v)

instance : SSZFixed Uint8 where
  size := 1
  enc_size := Uint8.encU_length

instance : SSZCodec Uint16 where
  enc := Uint16.encU
  dec := Uint16.decU
  isFixedSize := true
  maxSize := 2

instance : LawfulSSZ Uint16 where
  dec_enc := Uint16.decU_encU
  enc_size_le v := Nat.le_of_eq (Uint16.encU_length v)

instance : SSZFixed Uint16 where
  size := 2
  enc_size := Uint16.encU_length

instance : SSZCodec Uint32 where
  enc := Uint32.encU
  dec := Uint32.decU
  isFixedSize := true
  maxSize := 4

instance : LawfulSSZ Uint32 where
  dec_enc := Uint32.decU_encU
  enc_size_le v := Nat.le_of_eq (Uint32.encU_length v)

instance : SSZFixed Uint32 where
  size := 4
  enc_size := Uint32.encU_length

instance : SSZCodec Uint64 where
  enc := Uint64.encU
  dec := Uint64.decU
  isFixedSize := true
  maxSize := 8

instance : LawfulSSZ Uint64 where
  dec_enc := Uint64.decU_encU
  enc_size_le v := Nat.le_of_eq (Uint64.encU_length v)

instance : SSZFixed Uint64 where
  size := 8
  enc_size := Uint64.encU_length

instance : SSZPositive Uint8 := ⟨Nat.one_pos⟩
instance : SSZPositive Uint16 := ⟨by decide⟩
instance : SSZPositive Uint32 := ⟨by decide⟩
instance : SSZPositive Uint64 := ⟨by decide⟩

end LeanSSZ
