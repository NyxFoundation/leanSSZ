/-
leanSpec devnet container set — fixed-size containers and the KoalaBear
field element.

Shapes are pinned by the leanSpec devnet SSZ fixtures
(`fixtures/consensus/ssz/devnet/ssz/`); byte widths cross-checked against
each fixture's `serialized` length. XMSS signatures appear on the wire as
an opaque fixed 424-byte blob under the test parameter set, so `Signature`
is `BytesN 424` here.

Every container follows the mechanical template:
  - `toParts` / `schema`, `enc := assemble`, `dec := disassemble + field
    decodes`;
  - roundtrip = `disassemble_assemble` + `dec_enc` per field;
  - `hash_tree_root` = merkleize over the field roots.
-/

import LeanSSZ.Core.ContainerCodec
import LeanSSZ.Merkle.Root

namespace LeanSSZ
namespace Devnet

open Container

/-! ## KoalaBear field element (XMSS public keys) -/

/-- KoalaBear prime `2^31 - 2^24 + 1`. -/
def fpP : Nat := 2130706433

/-- KoalaBear field element: 4-byte LE on the wire, value < p. -/
def Fp := { v : UInt32 // v.toNat < fpP }

namespace Fp

instance : Inhabited Fp := ⟨⟨0, by decide⟩⟩
instance : Repr Fp := ⟨fun v p => reprPrec v.val p⟩
instance : BEq Fp := ⟨fun a b => a.val == b.val⟩

def encF (v : Fp) : List UInt8 := LE.encodeNat v.val.toNat 4

def decF (bs : List UInt8) : Except SSZError Fp :=
  if h : bs.length = 4 ∧ LE.decodeNat bs < fpP then
    .ok ⟨UInt32.ofNat (LE.decodeNat bs), by
      have hlt : LE.decodeNat bs < fpP := h.2
      have : LE.decodeNat bs < 2 ^ 32 := by
        have : fpP < 2 ^ 32 := by decide
        omega
      simpa [UInt32.toNat_ofNat_of_lt' this] using hlt⟩
  else
    .error (.invalidValue "Fp out of range or wrong width")

theorem encF_length (v : Fp) : (encF v).length = 4 := LE.encodeNat_length ..

theorem decF_encF (v : Fp) : decF (encF v) = .ok v := by
  obtain ⟨u, hu⟩ := v
  have hdec : LE.decodeNat (encF ⟨u, hu⟩) = u.toNat := by
    show LE.decodeNat (LE.encodeNat u.toNat 4) = u.toNat
    rw [LE.decodeNat_encodeNat]
    have h32 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    rw [h32]
    exact Nat.mod_eq_of_lt u.toNat_lt
  unfold decF
  rw [dif_pos (by rw [hdec]; exact ⟨encF_length _, hu⟩)]
  simp only [hdec]
  congr 1
  exact Subtype.ext UInt32.ofNat_toNat

end Fp

instance : SSZCodec Fp := ⟨Fp.encF, Fp.decF, true, 4⟩
instance : LawfulSSZ Fp :=
  ⟨Fp.decF_encF, fun v => Nat.le_of_eq (Fp.encF_length v)⟩
instance : SSZFixed Fp := ⟨4, Fp.encF_length⟩
instance : SSZPositive Fp := ⟨by decide⟩
instance : SSZBasic Fp := ⟨⟩
instance [Hasher] : HasHTR Fp :=
  ⟨fun x => Merkle.merkleize (Merkle.chunkify (enc x)) none⟩

/-! ## Type aliases pinned by devnet config -/

/-- XMSS signature under the test parameter set: opaque 424 bytes. -/
abbrev Signature := BytesN 424

instance : SSZPositive (BytesN 424) := ⟨by decide⟩

abbrev Slot := Uint64
abbrev ValidatorIndex := Uint64

end Devnet
end LeanSSZ
