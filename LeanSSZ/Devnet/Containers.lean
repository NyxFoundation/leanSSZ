/-
leanSpec devnet containers: codecs, roundtrip proofs, hash-tree-roots.

Field order and widths are pinned by the devnet SSZ fixtures. Every
container follows the same mechanical template (see `Checkpoint` for the
annotated version); the roundtrip proof is always `disassemble_assemble`
chained with per-field `dec_enc`.
-/

import LeanSSZ.Devnet.Basic

set_option maxRecDepth 4096

namespace LeanSSZ
namespace Devnet

open Container

/-! ## Checkpoint — the annotated template -/

structure Checkpoint where
  root : Bytes32
  slot : Slot
  deriving Repr

namespace Checkpoint

def toParts (c : Checkpoint) : List Part :=
  [fixedPart c.root, fixedPart c.slot]

def schema : List (Option Nat) := [some 32, some 8]

def encC (c : Checkpoint) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Checkpoint :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := Bytes32) s₁, dec (T := Uint64) s₂ with
    | .ok root, .ok slot => .ok ⟨root, slot⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Checkpoint) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : Checkpoint) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (40 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd = [enc c.root, enc c.slot] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : Checkpoint) : (encC c).length = 40 := by
  rw [encC, assemble_length _ (wf c)]
  show (40 : Nat) + 0 = 40
  rfl

end Checkpoint

instance : SSZCodec Checkpoint := ⟨Checkpoint.encC, Checkpoint.decC, true, 40⟩
instance : LawfulSSZ Checkpoint :=
  ⟨Checkpoint.decC_encC, fun c => Nat.le_of_eq (Checkpoint.encC_length c)⟩
instance : SSZFixed Checkpoint := ⟨40, Checkpoint.encC_length⟩
instance : SSZPositive Checkpoint := ⟨by decide⟩
instance [Hasher] : HasHTR Checkpoint :=
  ⟨fun c => Merkle.merkleize [htr c.root, htr c.slot] none⟩

end Devnet
end LeanSSZ

namespace LeanSSZ
namespace Devnet
open Container

/-! ## AttestationData -/

structure AttestationData where
  slot : Slot
  head : Checkpoint
  target : Checkpoint
  source : Checkpoint
  deriving Repr

namespace AttestationData

def toParts (c : AttestationData) : List Part :=
  [fixedPart c.slot, fixedPart c.head, fixedPart c.target, fixedPart c.source]

def schema : List (Option Nat) := [some 8, some 40, some 40, some 40]

def encC (c : AttestationData) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError AttestationData :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃, s₄] =>
    match dec (T := Uint64) s₁, dec (T := Checkpoint) s₂,
        dec (T := Checkpoint) s₃, dec (T := Checkpoint) s₄ with
    | .ok a, .ok b, .ok c, .ok d => .ok ⟨a, b, c, d⟩
    | .error e, _, _, _ => .error e
    | _, .error e, _, _ => .error e
    | _, _, .error e, _ => .error e
    | _, _, _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : AttestationData) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _
    (wfparts_cons_fixed _ wfparts_nil)))

theorem decC_encC (c : AttestationData) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (128 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.slot, enc c.head, enc c.target, enc c.source] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : AttestationData) : (encC c).length = 128 := by
  rw [encC, assemble_length _ (wf c)]
  show (128 : Nat) + 0 = 128
  rfl

end AttestationData

instance : SSZCodec AttestationData :=
  ⟨AttestationData.encC, AttestationData.decC, true, 128⟩
instance : LawfulSSZ AttestationData :=
  ⟨AttestationData.decC_encC, fun c => Nat.le_of_eq (AttestationData.encC_length c)⟩
instance : SSZFixed AttestationData := ⟨128, AttestationData.encC_length⟩
instance : SSZPositive AttestationData := ⟨by decide⟩
instance [Hasher] : HasHTR AttestationData :=
  ⟨fun c => Merkle.merkleize [htr c.slot, htr c.head, htr c.target, htr c.source] none⟩

/-! ## Attestation -/

structure Attestation where
  validatorId : ValidatorIndex
  data : AttestationData
  deriving Repr

namespace Attestation

def toParts (c : Attestation) : List Part :=
  [fixedPart c.validatorId, fixedPart c.data]

def schema : List (Option Nat) := [some 8, some 128]

def encC (c : Attestation) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Attestation :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := Uint64) s₁, dec (T := AttestationData) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Attestation) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : Attestation) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (136 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd = [enc c.validatorId, enc c.data] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : Attestation) : (encC c).length = 136 := by
  rw [encC, assemble_length _ (wf c)]
  show (136 : Nat) + 0 = 136
  rfl

end Attestation

instance : SSZCodec Attestation := ⟨Attestation.encC, Attestation.decC, true, 136⟩
instance : LawfulSSZ Attestation :=
  ⟨Attestation.decC_encC, fun c => Nat.le_of_eq (Attestation.encC_length c)⟩
instance : SSZFixed Attestation := ⟨136, Attestation.encC_length⟩
instance : SSZPositive Attestation := ⟨by decide⟩
instance [Hasher] : HasHTR Attestation :=
  ⟨fun c => Merkle.merkleize [htr c.validatorId, htr c.data] none⟩

/-! ## SignedAttestation -/

structure SignedAttestation where
  validatorId : ValidatorIndex
  data : AttestationData
  signature : Signature
  deriving Repr

namespace SignedAttestation

def toParts (c : SignedAttestation) : List Part :=
  [fixedPart c.validatorId, fixedPart c.data, fixedPart c.signature]

def schema : List (Option Nat) := [some 8, some 128, some 424]

def encC (c : SignedAttestation) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError SignedAttestation :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃] =>
    match dec (T := Uint64) s₁, dec (T := AttestationData) s₂,
        dec (T := Signature) s₃ with
    | .ok a, .ok b, .ok c => .ok ⟨a, b, c⟩
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : SignedAttestation) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil))

theorem decC_encC (c : SignedAttestation) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (560 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.validatorId, enc c.data, enc c.signature] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : SignedAttestation) : (encC c).length = 560 := by
  rw [encC, assemble_length _ (wf c)]
  show (560 : Nat) + 0 = 560
  rfl

end SignedAttestation

instance : SSZCodec SignedAttestation :=
  ⟨SignedAttestation.encC, SignedAttestation.decC, true, 560⟩
instance : LawfulSSZ SignedAttestation :=
  ⟨SignedAttestation.decC_encC, fun c => Nat.le_of_eq (SignedAttestation.encC_length c)⟩
instance : SSZFixed SignedAttestation := ⟨560, SignedAttestation.encC_length⟩
instance [Hasher] : HasHTR SignedAttestation :=
  ⟨fun c => Merkle.merkleize [htr c.validatorId, htr c.data, htr c.signature] none⟩

/-! ## Validator -/

structure Validator where
  attestationPubkey : BytesN 52
  proposalPubkey : BytesN 52
  index : ValidatorIndex
  deriving Repr

namespace Validator

def toParts (c : Validator) : List Part :=
  [fixedPart c.attestationPubkey, fixedPart c.proposalPubkey, fixedPart c.index]

def schema : List (Option Nat) := [some 52, some 52, some 8]

def encC (c : Validator) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Validator :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃] =>
    match dec (T := BytesN 52) s₁, dec (T := BytesN 52) s₂,
        dec (T := Uint64) s₃ with
    | .ok a, .ok b, .ok c => .ok ⟨a, b, c⟩
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Validator) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil))

theorem decC_encC (c : Validator) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (112 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.attestationPubkey, enc c.proposalPubkey, enc c.index] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : Validator) : (encC c).length = 112 := by
  rw [encC, assemble_length _ (wf c)]
  show (112 : Nat) + 0 = 112
  rfl

end Validator

instance : SSZCodec Validator := ⟨Validator.encC, Validator.decC, true, 112⟩
instance : LawfulSSZ Validator :=
  ⟨Validator.decC_encC, fun c => Nat.le_of_eq (Validator.encC_length c)⟩
instance : SSZFixed Validator := ⟨112, Validator.encC_length⟩
instance : SSZPositive Validator := ⟨by decide⟩
instance [Hasher] : HasHTR Validator :=
  ⟨fun c => Merkle.merkleize
    [htr c.attestationPubkey, htr c.proposalPubkey, htr c.index] none⟩

/-! ## Config -/

structure Config where
  genesisTime : Uint64
  deriving Repr

namespace Config

def toParts (c : Config) : List Part := [fixedPart c.genesisTime]

def schema : List (Option Nat) := [some 8]

def encC (c : Config) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Config :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁] =>
    match dec (T := Uint64) s₁ with
    | .ok a => .ok ⟨a⟩
    | .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Config) : WFParts (toParts c) :=
  wfparts_cons_fixed _ wfparts_nil

theorem decC_encC (c : Config) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (8 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd = [enc c.genesisTime] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : Config) : (encC c).length = 8 := by
  rw [encC, assemble_length _ (wf c)]
  show (8 : Nat) + 0 = 8
  rfl

end Config

instance : SSZCodec Config := ⟨Config.encC, Config.decC, true, 8⟩
instance : LawfulSSZ Config :=
  ⟨Config.decC_encC, fun c => Nat.le_of_eq (Config.encC_length c)⟩
instance : SSZFixed Config := ⟨8, Config.encC_length⟩
instance : SSZPositive Config := ⟨by decide⟩
instance [Hasher] : HasHTR Config :=
  ⟨fun c => Merkle.merkleize [htr c.genesisTime] none⟩

/-! ## BlockHeader -/

structure BlockHeader where
  slot : Slot
  proposerIndex : ValidatorIndex
  parentRoot : Bytes32
  stateRoot : Bytes32
  bodyRoot : Bytes32
  deriving Repr

namespace BlockHeader

def toParts (c : BlockHeader) : List Part :=
  [fixedPart c.slot, fixedPart c.proposerIndex, fixedPart c.parentRoot,
   fixedPart c.stateRoot, fixedPart c.bodyRoot]

def schema : List (Option Nat) := [some 8, some 8, some 32, some 32, some 32]

def encC (c : BlockHeader) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError BlockHeader :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃, s₄, s₅] =>
    match dec (T := Uint64) s₁, dec (T := Uint64) s₂, dec (T := Bytes32) s₃,
        dec (T := Bytes32) s₄, dec (T := Bytes32) s₅ with
    | .ok a, .ok b, .ok c, .ok d, .ok e => .ok ⟨a, b, c, d, e⟩
    | .error e, _, _, _, _ => .error e
    | _, .error e, _, _, _ => .error e
    | _, _, .error e, _, _ => .error e
    | _, _, _, .error e, _ => .error e
    | _, _, _, _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : BlockHeader) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _
    (wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil))))

theorem decC_encC (c : BlockHeader) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (112 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.slot, enc c.proposerIndex, enc c.parentRoot,
         enc c.stateRoot, enc c.bodyRoot] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : BlockHeader) : (encC c).length = 112 := by
  rw [encC, assemble_length _ (wf c)]
  show (112 : Nat) + 0 = 112
  rfl

end BlockHeader

instance : SSZCodec BlockHeader := ⟨BlockHeader.encC, BlockHeader.decC, true, 112⟩
instance : LawfulSSZ BlockHeader :=
  ⟨BlockHeader.decC_encC, fun c => Nat.le_of_eq (BlockHeader.encC_length c)⟩
instance : SSZFixed BlockHeader := ⟨112, BlockHeader.encC_length⟩
instance : SSZPositive BlockHeader := ⟨by decide⟩
instance [Hasher] : HasHTR BlockHeader :=
  ⟨fun c => Merkle.merkleize
    [htr c.slot, htr c.proposerIndex, htr c.parentRoot,
     htr c.stateRoot, htr c.bodyRoot] none⟩

/-! ## Status -/

structure Status where
  finalized : Checkpoint
  head : Checkpoint
  deriving Repr

namespace Status

def toParts (c : Status) : List Part :=
  [fixedPart c.finalized, fixedPart c.head]

def schema : List (Option Nat) := [some 40, some 40]

def encC (c : Status) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Status :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := Checkpoint) s₁, dec (T := Checkpoint) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Status) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : Status) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (80 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd = [enc c.finalized, enc c.head] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : Status) : (encC c).length = 80 := by
  rw [encC, assemble_length _ (wf c)]
  show (80 : Nat) + 0 = 80
  rfl

end Status

instance : SSZCodec Status := ⟨Status.encC, Status.decC, true, 80⟩
instance : LawfulSSZ Status :=
  ⟨Status.decC_encC, fun c => Nat.le_of_eq (Status.encC_length c)⟩
instance : SSZFixed Status := ⟨80, Status.encC_length⟩
instance [Hasher] : HasHTR Status :=
  ⟨fun c => Merkle.merkleize [htr c.finalized, htr c.head] none⟩

/-! ## PublicKey (XMSS, test parameter set) -/

structure PublicKey where
  root : SSZVector Fp 8
  parameter : SSZVector Fp 5

namespace PublicKey

def toParts (c : PublicKey) : List Part :=
  [fixedPart c.root, fixedPart c.parameter]

def schema : List (Option Nat) := [some 32, some 20]

def encC (c : PublicKey) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError PublicKey :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := SSZVector Fp 8) s₁, dec (T := SSZVector Fp 5) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : PublicKey) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : PublicKey) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c)
    (by show (52 : Nat) + 0 < 2 ^ 32; decide)
  have hsnd : (toParts c).map Prod.snd = [enc c.root, enc c.parameter] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_length (c : PublicKey) : (encC c).length = 52 := by
  rw [encC, assemble_length _ (wf c)]
  show (52 : Nat) + 0 = 52
  rfl

end PublicKey

instance : SSZCodec PublicKey := ⟨PublicKey.encC, PublicKey.decC, true, 52⟩
instance : LawfulSSZ PublicKey :=
  ⟨PublicKey.decC_encC, fun c => Nat.le_of_eq (PublicKey.encC_length c)⟩
instance : SSZFixed PublicKey := ⟨52, PublicKey.encC_length⟩
instance [Hasher] : HasHTR PublicKey :=
  ⟨fun c => Merkle.merkleize [htr c.root, htr c.parameter] none⟩

end Devnet
end LeanSSZ
