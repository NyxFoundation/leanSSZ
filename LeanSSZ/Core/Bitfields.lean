/-
SSZ bitfields: Bitvector (fixed bit count) and Bitlist (bounded, with
delimiter bit).

Mirrors `src/lean_spec/spec/ssz/bitfields.py` in leanSpec:
  - bits pack little-endian: bit `i` lands in byte `i / 8` at position
    `i % 8`;
  - Bitvector N encodes to exactly `⌈N / 8⌉` bytes, decode rejects
    non-zero padding bits (canonical encoding);
  - Bitlist appends a single 1 delimiter bit after the data bits, so the
    decoder can recover the bit count; decode rejects non-minimal byte
    counts.

Implementation: a bit list is packed into a `Nat` (`packBits`, bit `i` at
weight `2 ^ i`) and the existing little-endian machinery (`LE.encodeNat` /
`LE.decodeNat`) turns that into bytes. Canonicality checks become plain
arithmetic bounds:
  - Bitvector: value `< 2 ^ N` ⟺ all padding bits are zero;
  - Bitlist: `log2 value` is the delimiter position; the byte count must
    be exactly `log2 value / 8 + 1` (minimal), and the bit count is
    `log2 value`.
-/

import LeanSSZ.Core.Uint

namespace LeanSSZ

/-! ## Bit ↔ Nat packing -/

namespace Bits

/-- Pack a bit list into a `Nat`, bit `i` at weight `2 ^ i`. -/
def packBits : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * packBits rest

/-- Read the lowest `len` bits of a `Nat` as a bit list. -/
def unpackBits (v : Nat) : Nat → List Bool
  | 0 => []
  | len + 1 => (v % 2 == 1) :: unpackBits (v / 2) len

theorem packBits_lt (bits : List Bool) : packBits bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [packBits]
  | cons b rest ih =>
    show (if b then 1 else 0) + 2 * packBits rest < 2 ^ (rest.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2]
    cases b <;> simp <;> omega

theorem unpackBits_length (v len : Nat) : (unpackBits v len).length = len := by
  induction len generalizing v with
  | zero => rfl
  | succ len ih => simp [unpackBits, ih]

/-- Unpacking sees only the lowest `len` bits: any multiple of `2 ^ len`
added on top (e.g. a Bitlist delimiter) is invisible. -/
theorem unpackBits_packBits_add (bits : List Bool) (c : Nat) :
    unpackBits (packBits bits + 2 ^ bits.length * c) bits.length = bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b rest ih =>
    have hval : packBits (b :: rest) + 2 ^ (rest.length + 1) * c
        = (if b then 1 else 0) + 2 * (packBits rest + 2 ^ rest.length * c) := by
      show (if b then 1 else 0) + 2 * packBits rest + 2 ^ (rest.length + 1) * c = _
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, Nat.mul_assoc]
      omega
    show unpackBits (packBits (b :: rest) + 2 ^ (rest.length + 1) * c)
        (rest.length + 1) = b :: rest
    rw [hval]
    cases b
    · have e1 : (if (false : Bool) then (1 : Nat) else 0)
          + 2 * (packBits rest + 2 ^ rest.length * c)
          = 2 * (packBits rest + 2 ^ rest.length * c) := by simp
      rw [e1]
      show ((2 * (packBits rest + 2 ^ rest.length * c)) % 2 == 1)
          :: unpackBits ((2 * (packBits rest + 2 ^ rest.length * c)) / 2) rest.length
          = false :: rest
      have h1 : (2 * (packBits rest + 2 ^ rest.length * c)) % 2 = 0 := by omega
      have h2 : (2 * (packBits rest + 2 ^ rest.length * c)) / 2
          = packBits rest + 2 ^ rest.length * c := by omega
      simp [h1, h2, ih c]
    · have e1 : (if (true : Bool) then (1 : Nat) else 0)
          + 2 * (packBits rest + 2 ^ rest.length * c)
          = 1 + 2 * (packBits rest + 2 ^ rest.length * c) := by simp
      rw [e1]
      show ((1 + 2 * (packBits rest + 2 ^ rest.length * c)) % 2 == 1)
          :: unpackBits ((1 + 2 * (packBits rest + 2 ^ rest.length * c)) / 2) rest.length
          = true :: rest
      have h1 : (1 + 2 * (packBits rest + 2 ^ rest.length * c)) % 2 = 1 := by omega
      have h2 : (1 + 2 * (packBits rest + 2 ^ rest.length * c)) / 2
          = packBits rest + 2 ^ rest.length * c := by omega
      simp [h1, h2, ih c]

theorem unpackBits_packBits (bits : List Bool) :
    unpackBits (packBits bits) bits.length = bits := by
  simpa using unpackBits_packBits_add bits 0

/-- `Nat.log2` is pinned by a two-sided power bracket. -/
theorem log2_eq {L n : Nat} (h1 : 2 ^ L ≤ n) (h2 : n < 2 ^ (L + 1)) :
    n.log2 = L := by
  have hn : n ≠ 0 := by
    have : (0 : Nat) < 2 ^ L := Nat.pow_pos (n := L) (by decide)
    omega
  have ha : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn
  have hb : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  rcases Nat.lt_trichotomy n.log2 L with h | h | h
  · exfalso
    have : 2 ^ (n.log2 + 1) ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by decide) h
    omega
  · exact h
  · exfalso
    have : 2 ^ (L + 1) ≤ 2 ^ n.log2 :=
      Nat.pow_le_pow_right (by decide) h
    omega

/-- `256 ^ k` as a power of two. -/
theorem pow256_eq (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-! ### Fast execution path (`@[csimp]`)

The `Nat`-packing definitions above are the proof substrate, but packing
thousands of bits into one big natural is quadratic at runtime. The
byte-at-a-time implementations below are proven equal and installed with
`@[csimp]`, so compiled code runs them while every theorem still talks
about the originals. -/

/-- Byte-wise packing: each output byte packs 8 bits (small-`Nat`
arithmetic only — no bignums). -/
def bytesOfBits : List Bool → List UInt8
  | [] => []
  | bits@(_ :: _) =>
    UInt8.ofNat (packBits (bits.take 8)) :: bytesOfBits (bits.drop 8)
  termination_by bits => bits.length
  decreasing_by
    subst bits
    simp [List.length_drop]
    omega

theorem packBits_append (l₁ l₂ : List Bool) :
    packBits (l₁ ++ l₂) = packBits l₁ + 2 ^ l₁.length * packBits l₂ := by
  induction l₁ with
  | nil => simp [packBits]
  | cons b rest ih =>
    show (if b then 1 else 0) + 2 * packBits (rest ++ l₂)
        = (if b then 1 else 0) + 2 * packBits rest
          + 2 ^ (rest.length + 1) * packBits l₂
    rw [ih, Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, Nat.mul_assoc]
    omega

theorem bytesOfBits_eq : ∀ (bits : List Bool),
    bytesOfBits bits = LE.encodeNat (packBits bits) ((bits.length + 7) / 8)
  | [] => by simp [bytesOfBits, packBits, LE.encodeNat]
  | b :: t => by
    have ih := bytesOfBits_eq ((b :: t).drop 8)
    have hsplit := packBits_append ((b :: t).take 8) ((b :: t).drop 8)
    rw [List.take_append_drop] at hsplit
    have ha : packBits ((b :: t).take 8) < 256 := by
      have h1 := packBits_lt ((b :: t).take 8)
      have h2 : ((b :: t).take 8).length ≤ 8 := by
        simp only [List.length_take]
        omega
      have h3 : 2 ^ ((b :: t).take 8).length ≤ 2 ^ 8 :=
        Nat.pow_le_pow_right (by decide) h2
      omega
    have hv : packBits (b :: t)
        = packBits ((b :: t).take 8) + 256 * packBits ((b :: t).drop 8) := by
      by_cases h8 : 8 ≤ (b :: t).length
      · have ht : ((b :: t).take 8).length = 8 := by
          simp only [List.length_take, List.length_cons]
          simp only [List.length_cons] at h8
          omega
        rw [ht, show (2:Nat) ^ 8 = 256 from by decide] at hsplit
        omega
      · have hd : (b :: t).drop 8 = [] := List.drop_eq_nil_of_le (by
          simp only [List.length_cons]
          simp only [List.length_cons] at h8
          omega)
        rw [hd] at hsplit ⊢
        show packBits (b :: t) = _ + 256 * packBits []
        simp [packBits] at hsplit ⊢
        omega
    have hk : ((b :: t).length + 7) / 8 = (((b :: t).drop 8).length + 7) / 8 + 1 := by
      simp only [List.length_drop, List.length_cons]
      omega
    have hm : packBits (b :: t) % 256 = packBits ((b :: t).take 8) := by omega
    have hd : packBits (b :: t) / 256 = packBits ((b :: t).drop 8) := by omega
    rw [show bytesOfBits (b :: t)
        = UInt8.ofNat (packBits ((b :: t).take 8)) :: bytesOfBits ((b :: t).drop 8)
        from by rw [bytesOfBits]]
    rw [hk]
    show _ = UInt8.ofNat (packBits (b :: t) % 256)
        :: LE.encodeNat (packBits (b :: t) / 256) ((((b :: t).drop 8).length + 7) / 8)
    rw [hm, hd, ih]
  termination_by bits => bits.length
  decreasing_by
    simp [List.length_drop]
    omega


/-- The packed byte form of a bit list (no delimiter) — shared by the
codec and `hash_tree_root`. -/
def packedBytes (bits : List Bool) : List UInt8 :=
  LE.encodeNat (packBits bits) ((bits.length + 7) / 8)

@[csimp]
theorem packedBytes_eq_fast : @packedBytes = @bytesOfBits := by
  funext bits
  rw [packedBytes, bytesOfBits_eq]

end Bits

/-! ## Bitvector -/

/-- Fixed-length SSZ bitfield with exactly `n` bits. -/
structure Bitvector (n : Nat) where
  data : List Bool
  length_eq : data.length = n

namespace Bitvector

variable {n : Nat}

instance : Inhabited (Bitvector n) := ⟨⟨List.replicate n false, by simp⟩⟩

def encBV (v : Bitvector n) : List UInt8 :=
  LE.encodeNat (Bits.packBits v.data) ((n + 7) / 8)

def decBV (bs : List UInt8) : Except SSZError (Bitvector n) :=
  if bs.length = (n + 7) / 8 then
    let val := LE.decodeNat bs
    if val < 2 ^ n then
      .ok ⟨Bits.unpackBits val n, Bits.unpackBits_length ..⟩
    else
      .error (.invalidValue "non-zero padding bits in bitvector")
  else
    .error (.invalidLength ((n + 7) / 8) bs.length)

theorem encBV_length (v : Bitvector n) : (encBV v).length = (n + 7) / 8 :=
  LE.encodeNat_length ..

theorem decBV_encBV (v : Bitvector n) : decBV (encBV v) = .ok v := by
  obtain ⟨data, hlen⟩ := v
  subst hlen
  have hpack : Bits.packBits data < 2 ^ data.length := Bits.packBits_lt data
  have hval : LE.decodeNat (encBV ⟨data, rfl⟩) = Bits.packBits data := by
    show LE.decodeNat (LE.encodeNat (Bits.packBits data) ((data.length + 7) / 8))
        = Bits.packBits data
    rw [LE.decodeNat_encodeNat, Bits.pow256_eq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hpack
      (Nat.pow_le_pow_right (by decide) (by omega)))
  unfold decBV
  rw [if_pos (encBV_length ⟨data, rfl⟩)]
  simp only [hval, if_pos hpack, Bits.unpackBits_packBits]

/-- Fast encoder: byte-wise packing. -/
def encBVf {n : Nat} (v : Bitvector n) : List UInt8 :=
  Bits.bytesOfBits v.data

@[csimp]
theorem encBV_eq_fast : @encBV = @encBVf := by
  funext n v
  rw [encBVf, Bits.bytesOfBits_eq, encBV, v.length_eq]

end Bitvector

instance {n : Nat} : SSZCodec (Bitvector n) where
  enc := Bitvector.encBV
  dec := Bitvector.decBV
  isFixedSize := true
  maxSize := (n + 7) / 8

instance {n : Nat} : LawfulSSZ (Bitvector n) where
  dec_enc := Bitvector.decBV_encBV
  enc_size_le v := Nat.le_of_eq (Bitvector.encBV_length v)

instance {n : Nat} : SSZFixed (Bitvector n) where
  size := (n + 7) / 8
  enc_size := Bitvector.encBV_length

/-! ## Bitlist -/

/-- Variable-length SSZ bitfield with 0 to `limit` bits. -/
structure Bitlist (limit : Nat) where
  data : List Bool
  le_limit : data.length ≤ limit

namespace Bitlist

variable {limit : Nat}

instance : Inhabited (Bitlist limit) := ⟨⟨[], Nat.zero_le _⟩⟩

/-- Delimiter bit at position `data.length`, then LE bytes, minimal count. -/
def encBL (l : Bitlist limit) : List UInt8 :=
  LE.encodeNat (Bits.packBits l.data + 2 ^ l.data.length) (l.data.length / 8 + 1)

def decBL (bs : List UInt8) : Except SSZError (Bitlist limit) :=
  let val := LE.decodeNat bs
  if val = 0 then
    .error (.invalidValue "bitlist missing delimiter bit")
  else
    if h : bs.length = val.log2 / 8 + 1 ∧ val.log2 ≤ limit then
      .ok ⟨Bits.unpackBits val val.log2, by
        rw [Bits.unpackBits_length]; exact h.2⟩
    else
      .error (.invalidValue "bitlist byte count not minimal or over limit")

theorem encBL_length (l : Bitlist limit) :
    (encBL l).length = l.data.length / 8 + 1 :=
  LE.encodeNat_length ..

theorem encBL_length_le (l : Bitlist limit) :
    (encBL l).length ≤ limit / 8 + 1 := by
  rw [encBL_length]
  have h8 : l.data.length / 8 ≤ limit / 8 := Nat.div_le_div_right l.le_limit
  omega

theorem decBL_encBL (l : Bitlist limit) : decBL (encBL l) = .ok l := by
  obtain ⟨data, hle⟩ := l
  have hpack : Bits.packBits data < 2 ^ data.length := Bits.packBits_lt data
  have hval : LE.decodeNat (encBL ⟨data, hle⟩)
      = Bits.packBits data + 2 ^ data.length := by
    show LE.decodeNat (LE.encodeNat (Bits.packBits data + 2 ^ data.length)
        (data.length / 8 + 1)) = _
    rw [LE.decodeNat_encodeNat, Bits.pow256_eq]
    apply Nat.mod_eq_of_lt
    have hbound : Bits.packBits data + 2 ^ data.length < 2 ^ (data.length + 1) := by
      rw [Nat.pow_succ]
      omega
    exact Nat.lt_of_lt_of_le hbound
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hne : Bits.packBits data + 2 ^ data.length ≠ 0 := by
    have : (0 : Nat) < 2 ^ data.length := Nat.pow_pos (by decide)
    omega
  have hlog : (Bits.packBits data + 2 ^ data.length).log2 = data.length :=
    Bits.log2_eq (by omega) (by rw [Nat.pow_succ]; omega)
  have hcond : (encBL (limit := limit) ⟨data, hle⟩).length
      = (Bits.packBits data + 2 ^ data.length).log2 / 8 + 1
      ∧ (Bits.packBits data + 2 ^ data.length).log2 ≤ limit := by
    constructor
    · rw [encBL_length, hlog]
    · rw [hlog]; exact hle
  have hunpack : Bits.unpackBits (Bits.packBits data + 2 ^ data.length)
      data.length = data := by
    have := Bits.unpackBits_packBits_add data 1
    simpa using this
  unfold decBL
  simp only [hval, if_neg hne, hlog, hunpack]
  rw [dif_pos ⟨encBL_length (limit := limit) ⟨data, hle⟩, hle⟩]

/-- Fast encoder: append the delimiter bit, pack byte-wise. -/
def encBLf {limit : Nat} (l : Bitlist limit) : List UInt8 :=
  Bits.bytesOfBits (l.data ++ [true])

@[csimp]
theorem encBL_eq_fast : @encBL = @encBLf := by
  funext limit l
  have h1 : Bits.packBits (l.data ++ [true])
      = Bits.packBits l.data + 2 ^ l.data.length := by
    rw [Bits.packBits_append]
    simp [Bits.packBits]
  have h2 : ((l.data ++ [true]).length + 7) / 8 = l.data.length / 8 + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [encBL, encBLf, Bits.bytesOfBits_eq, h1, h2]

end Bitlist

instance {limit : Nat} : SSZCodec (Bitlist limit) where
  enc := Bitlist.encBL
  dec := Bitlist.decBL
  isFixedSize := false
  maxSize := limit / 8 + 1

instance {limit : Nat} : LawfulSSZ (Bitlist limit) where
  dec_enc := Bitlist.decBL_encBL
  enc_size_le := Bitlist.encBL_length_le

end LeanSSZ

