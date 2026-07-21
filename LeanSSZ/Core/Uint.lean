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

Each width `w ∈ {8, 16, 32, 64}` gets `encode` (exactly `w / 8` LE bytes),
`decode` (rejects any other length), the roundtrip theorem, and
`SSZType` / `LawfulSSZ` instances. The bodies are deliberately identical
modulo the width; a macro would obscure more than it saves at four sites.
-/

abbrev Uint8 := UInt8
abbrev Uint16 := UInt16
abbrev Uint32 := UInt32
abbrev Uint64 := UInt64

namespace Uint8

def encode (v : Uint8) : ByteArray :=
  ⟨(LE.encodeNat v.toNat 1).toArray⟩

def decode (bs : ByteArray) : Except SSZError Uint8 :=
  if bs.size = 1 then
    .ok (UInt8.ofNat (LE.decodeNat bs.data.toList))
  else
    .error (.invalidLength 1 bs.size)

theorem encode_size (v : Uint8) : (encode v).size = 1 := by
  show (LE.encodeNat v.toNat 1).toArray.size = 1
  rw [List.size_toArray, LE.encodeNat_length]

theorem decode_encode (v : Uint8) : decode (encode v) = .ok v := by
  unfold decode
  rw [if_pos (encode_size v)]
  congr 1
  show UInt8.ofNat (LE.decodeNat (LE.encodeNat v.toNat 1).toArray.toList) = v
  rw [List.toList_toArray, LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 1 = 2 ^ 8 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt8.ofNat_toNat

end Uint8

namespace Uint16

def encode (v : Uint16) : ByteArray :=
  ⟨(LE.encodeNat v.toNat 2).toArray⟩

def decode (bs : ByteArray) : Except SSZError Uint16 :=
  if bs.size = 2 then
    .ok (UInt16.ofNat (LE.decodeNat bs.data.toList))
  else
    .error (.invalidLength 2 bs.size)

theorem encode_size (v : Uint16) : (encode v).size = 2 := by
  show (LE.encodeNat v.toNat 2).toArray.size = 2
  rw [List.size_toArray, LE.encodeNat_length]

theorem decode_encode (v : Uint16) : decode (encode v) = .ok v := by
  unfold decode
  rw [if_pos (encode_size v)]
  congr 1
  show UInt16.ofNat (LE.decodeNat (LE.encodeNat v.toNat 2).toArray.toList) = v
  rw [List.toList_toArray, LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt16.ofNat_toNat

end Uint16

namespace Uint32

def encode (v : Uint32) : ByteArray :=
  ⟨(LE.encodeNat v.toNat 4).toArray⟩

def decode (bs : ByteArray) : Except SSZError Uint32 :=
  if bs.size = 4 then
    .ok (UInt32.ofNat (LE.decodeNat bs.data.toList))
  else
    .error (.invalidLength 4 bs.size)

theorem encode_size (v : Uint32) : (encode v).size = 4 := by
  show (LE.encodeNat v.toNat 4).toArray.size = 4
  rw [List.size_toArray, LE.encodeNat_length]

theorem decode_encode (v : Uint32) : decode (encode v) = .ok v := by
  unfold decode
  rw [if_pos (encode_size v)]
  congr 1
  show UInt32.ofNat (LE.decodeNat (LE.encodeNat v.toNat 4).toArray.toList) = v
  rw [List.toList_toArray, LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt32.ofNat_toNat

end Uint32

namespace Uint64

/-- SSZ-2: a Uint64 value lies in [0, 2^64). -/
theorem range (v : Uint64) : v.toNat < 2 ^ 64 :=
  v.toNat_lt

def encode (v : Uint64) : ByteArray :=
  ⟨(LE.encodeNat v.toNat 8).toArray⟩

def decode (bs : ByteArray) : Except SSZError Uint64 :=
  if bs.size = 8 then
    .ok (UInt64.ofNat (LE.decodeNat bs.data.toList))
  else
    .error (.invalidLength 8 bs.size)

theorem encode_size (v : Uint64) : (encode v).size = 8 := by
  show (LE.encodeNat v.toNat 8).toArray.size = 8
  rw [List.size_toArray, LE.encodeNat_length]

/-- SSZ-3: a Uint64 is recovered by 8-byte LE encode/decode. -/
theorem decode_encode (v : Uint64) : decode (encode v) = .ok v := by
  unfold decode
  rw [if_pos (encode_size v)]
  congr 1
  show UInt64.ofNat (LE.decodeNat (LE.encodeNat v.toNat 8).toArray.toList) = v
  rw [List.toList_toArray, LE.decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt64.ofNat_toNat

end Uint64

instance : SSZType Uint8 where
  serialize := Uint8.encode
  deserialize := Uint8.decode
  isFixedSize := true
  maxSize := 1

instance : LawfulSSZ Uint8 where
  decode_encode := Uint8.decode_encode
  encode_size_le_max v := Nat.le_of_eq (Uint8.encode_size v)

instance : SSZType Uint16 where
  serialize := Uint16.encode
  deserialize := Uint16.decode
  isFixedSize := true
  maxSize := 2

instance : LawfulSSZ Uint16 where
  decode_encode := Uint16.decode_encode
  encode_size_le_max v := Nat.le_of_eq (Uint16.encode_size v)

instance : SSZType Uint32 where
  serialize := Uint32.encode
  deserialize := Uint32.decode
  isFixedSize := true
  maxSize := 4

instance : LawfulSSZ Uint32 where
  decode_encode := Uint32.decode_encode
  encode_size_le_max v := Nat.le_of_eq (Uint32.encode_size v)

instance : SSZType Uint64 where
  serialize := Uint64.encode
  deserialize := Uint64.decode
  isFixedSize := true
  maxSize := 8

instance : LawfulSSZ Uint64 where
  decode_encode := Uint64.decode_encode
  encode_size_le_max v := Nat.le_of_eq (Uint64.encode_size v)

end LeanSSZ
