/-
leanSpec devnet containers with variable-size fields.

Same mechanical template as `Containers.lean`; the size bound now uses
`enc_size_le` per variable field (the numerals are each field type's
`maxSize`, accepted by definitional unfolding).
-/

import LeanSSZ.Devnet.Containers

set_option maxRecDepth 8192

namespace LeanSSZ
namespace Devnet

open Container

/-- Participation bitlist, capacity = validator registry limit (2^12). -/
abbrev AggregationBits := Bitlist 4096

/-! ## AggregatedAttestation -/

structure AggregatedAttestation where
  aggregationBits : AggregationBits
  data : AttestationData


namespace AggregatedAttestation

def toParts (c : AggregatedAttestation) : List Part :=
  [varPart c.aggregationBits, fixedPart c.data]

def schema : List (Option Nat) := [none, some 128]

def encC (c : AggregatedAttestation) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError AggregatedAttestation :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := AggregationBits) s₁, dec (T := AttestationData) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : AggregatedAttestation) : WFParts (toParts c) :=
  wfparts_cons_var _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : AggregatedAttestation) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb : (enc c.aggregationBits).length ≤ 513 := enc_size_le c.aggregationBits
    rw [show fixedLen ((toParts c).map Prod.fst) = 132 from rfl,
        show varTotal (toParts c) = (enc c.aggregationBits).length + 0 from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd = [enc c.aggregationBits, enc c.data] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : AggregatedAttestation) : (encC c).length ≤ 645 := by
  rw [encC, assemble_length _ (wf c)]
  have hb : (enc c.aggregationBits).length ≤ 513 := enc_size_le c.aggregationBits
  rw [show fixedLen ((toParts c).map Prod.fst) = 132 from rfl,
      show varTotal (toParts c) = (enc c.aggregationBits).length + 0 from rfl]
  omega

end AggregatedAttestation

instance : SSZCodec AggregatedAttestation :=
  ⟨AggregatedAttestation.encC, AggregatedAttestation.decC, false, 645⟩
instance : LawfulSSZ AggregatedAttestation :=
  ⟨AggregatedAttestation.decC_encC, AggregatedAttestation.encC_size_le⟩
instance [Hasher] : HasHTR AggregatedAttestation :=
  ⟨fun c => Merkle.merkleize [htr c.aggregationBits, htr c.data] none⟩

/-- Block-body attestation list (limit 2^12), variable-size elements. -/
abbrev AggregatedAttestations := SSZList AggregatedAttestation 4096

instance : SSZOffsetsFit AggregatedAttestation 4096 := ⟨by decide⟩

/-! ## BlockBody -/

structure BlockBody where
  attestations : AggregatedAttestations

namespace BlockBody

def toParts (c : BlockBody) : List Part := [varPart c.attestations]

def schema : List (Option Nat) := [none]

def encC (c : BlockBody) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError BlockBody :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁] =>
    match dec (T := AggregatedAttestations) s₁ with
    | .ok a => .ok ⟨a⟩
    | .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : BlockBody) : WFParts (toParts c) :=
  wfparts_cons_var _ wfparts_nil

theorem decC_encC (c : BlockBody) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb : (enc c.attestations).length ≤ 2658304 := enc_size_le c.attestations
    rw [show fixedLen ((toParts c).map Prod.fst) = 4 from rfl,
        show varTotal (toParts c) = (enc c.attestations).length + 0 from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd = [enc c.attestations] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : BlockBody) : (encC c).length ≤ 2658308 := by
  rw [encC, assemble_length _ (wf c)]
  have hb : (enc c.attestations).length ≤ 2658304 := enc_size_le c.attestations
  rw [show fixedLen ((toParts c).map Prod.fst) = 4 from rfl,
      show varTotal (toParts c) = (enc c.attestations).length + 0 from rfl]
  omega

end BlockBody

instance : SSZCodec BlockBody := ⟨BlockBody.encC, BlockBody.decC, false, 2658308⟩
instance : LawfulSSZ BlockBody := ⟨BlockBody.decC_encC, BlockBody.encC_size_le⟩
instance [Hasher] : HasHTR BlockBody :=
  ⟨fun c => Merkle.merkleize [htr c.attestations] none⟩

/-! ## Block -/

structure Block where
  slot : Slot
  proposerIndex : ValidatorIndex
  parentRoot : Bytes32
  stateRoot : Bytes32
  body : BlockBody

namespace Block

def toParts (c : Block) : List Part :=
  [fixedPart c.slot, fixedPart c.proposerIndex, fixedPart c.parentRoot,
   fixedPart c.stateRoot, varPart c.body]

def schema : List (Option Nat) := [some 8, some 8, some 32, some 32, none]

def encC (c : Block) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError Block :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃, s₄, s₅] =>
    match dec (T := Uint64) s₁, dec (T := Uint64) s₂, dec (T := Bytes32) s₃,
        dec (T := Bytes32) s₄, dec (T := BlockBody) s₅ with
    | .ok a, .ok b, .ok c, .ok d, .ok e => .ok ⟨a, b, c, d, e⟩
    | .error e, _, _, _, _ => .error e
    | _, .error e, _, _, _ => .error e
    | _, _, .error e, _, _ => .error e
    | _, _, _, .error e, _ => .error e
    | _, _, _, _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : Block) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _
    (wfparts_cons_fixed _ (wfparts_cons_var _ wfparts_nil))))

theorem decC_encC (c : Block) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb : (enc c.body).length ≤ 2658308 := enc_size_le c.body
    rw [show fixedLen ((toParts c).map Prod.fst) = 84 from rfl,
        show varTotal (toParts c) = (enc c.body).length + 0 from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.slot, enc c.proposerIndex, enc c.parentRoot,
         enc c.stateRoot, enc c.body] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : Block) : (encC c).length ≤ 2658392 := by
  rw [encC, assemble_length _ (wf c)]
  have hb : (enc c.body).length ≤ 2658308 := enc_size_le c.body
  rw [show fixedLen ((toParts c).map Prod.fst) = 84 from rfl,
      show varTotal (toParts c) = (enc c.body).length + 0 from rfl]
  omega

end Block

instance : SSZCodec Block := ⟨Block.encC, Block.decC, false, 2658392⟩
instance : LawfulSSZ Block := ⟨Block.decC_encC, Block.encC_size_le⟩
instance [Hasher] : HasHTR Block :=
  ⟨fun c => Merkle.merkleize
    [htr c.slot, htr c.proposerIndex, htr c.parentRoot,
     htr c.stateRoot, htr c.body] none⟩

/-! ## AggregatedSignatureProof -/

structure AggregatedSignatureProof where
  participants : AggregationBits
  proofData : ByteList512KiB

namespace AggregatedSignatureProof

def toParts (c : AggregatedSignatureProof) : List Part :=
  [varPart c.participants, varPart c.proofData]

def schema : List (Option Nat) := [none, none]

def encC (c : AggregatedSignatureProof) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError AggregatedSignatureProof :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := AggregationBits) s₁, dec (T := ByteList512KiB) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : AggregatedSignatureProof) : WFParts (toParts c) :=
  wfparts_cons_var _ (wfparts_cons_var _ wfparts_nil)

theorem decC_encC (c : AggregatedSignatureProof) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb₁ : (enc c.participants).length ≤ 513 := enc_size_le c.participants
    have hb₂ : (enc c.proofData).length ≤ 524288 := enc_size_le c.proofData
    rw [show fixedLen ((toParts c).map Prod.fst) = 8 from rfl,
        show varTotal (toParts c)
          = (enc c.participants).length + ((enc c.proofData).length + 0) from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.participants, enc c.proofData] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : AggregatedSignatureProof) :
    (encC c).length ≤ 524809 := by
  rw [encC, assemble_length _ (wf c)]
  have hb₁ : (enc c.participants).length ≤ 513 := enc_size_le c.participants
  have hb₂ : (enc c.proofData).length ≤ 524288 := enc_size_le c.proofData
  rw [show fixedLen ((toParts c).map Prod.fst) = 8 from rfl,
      show varTotal (toParts c)
        = (enc c.participants).length + ((enc c.proofData).length + 0) from rfl]
  omega

end AggregatedSignatureProof

instance : SSZCodec AggregatedSignatureProof :=
  ⟨AggregatedSignatureProof.encC, AggregatedSignatureProof.decC, false, 524809⟩
instance : LawfulSSZ AggregatedSignatureProof :=
  ⟨AggregatedSignatureProof.decC_encC, AggregatedSignatureProof.encC_size_le⟩
instance [Hasher] : HasHTR AggregatedSignatureProof :=
  ⟨fun c => Merkle.merkleize [htr c.participants, htr c.proofData] none⟩

/-- Attestation signature list (limit 2^12): aggregated signature proofs,
variable-size elements (offset-table layout). -/
abbrev AttestationSignatures := SSZList AggregatedSignatureProof 4096

instance : SSZOffsetsFit AggregatedSignatureProof 4096 := ⟨by decide⟩

/-! ## BlockSignatures -/

structure BlockSignatures where
  attestationSignatures : AttestationSignatures
  proposerSignature : Signature

namespace BlockSignatures

def toParts (c : BlockSignatures) : List Part :=
  [varPart c.attestationSignatures, fixedPart c.proposerSignature]

def schema : List (Option Nat) := [none, some 424]

def encC (c : BlockSignatures) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError BlockSignatures :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := AttestationSignatures) s₁, dec (T := Signature) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : BlockSignatures) : WFParts (toParts c) :=
  wfparts_cons_var _ (wfparts_cons_fixed _ wfparts_nil)

theorem decC_encC (c : BlockSignatures) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb : (enc c.attestationSignatures).length ≤ 2149634048 :=
      enc_size_le c.attestationSignatures
    rw [show fixedLen ((toParts c).map Prod.fst) = 428 from rfl,
        show varTotal (toParts c)
          = (enc c.attestationSignatures).length + 0 from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.attestationSignatures, enc c.proposerSignature] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : BlockSignatures) : (encC c).length ≤ 2149634476 := by
  rw [encC, assemble_length _ (wf c)]
  have hb : (enc c.attestationSignatures).length ≤ 2149634048 :=
    enc_size_le c.attestationSignatures
  rw [show fixedLen ((toParts c).map Prod.fst) = 428 from rfl,
      show varTotal (toParts c)
        = (enc c.attestationSignatures).length + 0 from rfl]
  omega

end BlockSignatures

instance : SSZCodec BlockSignatures :=
  ⟨BlockSignatures.encC, BlockSignatures.decC, false, 2149634476⟩
instance : LawfulSSZ BlockSignatures :=
  ⟨BlockSignatures.decC_encC, BlockSignatures.encC_size_le⟩
instance [Hasher] : HasHTR BlockSignatures :=
  ⟨fun c => Merkle.merkleize
    [htr c.attestationSignatures, htr c.proposerSignature] none⟩

/-! ## SignedBlock -/

structure SignedBlock where
  message : Block
  signature : BlockSignatures

namespace SignedBlock

def toParts (c : SignedBlock) : List Part :=
  [varPart c.message, varPart c.signature]

def schema : List (Option Nat) := [none, none]

def encC (c : SignedBlock) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError SignedBlock :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂] =>
    match dec (T := Block) s₁, dec (T := BlockSignatures) s₂ with
    | .ok a, .ok b => .ok ⟨a, b⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : SignedBlock) : WFParts (toParts c) :=
  wfparts_cons_var _ (wfparts_cons_var _ wfparts_nil)

theorem decC_encC (c : SignedBlock) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb₁ : (enc c.message).length ≤ 2658392 := enc_size_le c.message
    have hb₂ : (enc c.signature).length ≤ 2149634476 := enc_size_le c.signature
    rw [show fixedLen ((toParts c).map Prod.fst) = 8 from rfl,
        show varTotal (toParts c)
          = (enc c.message).length + ((enc c.signature).length + 0) from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd = [enc c.message, enc c.signature] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : SignedBlock) : (encC c).length ≤ 2152292876 := by
  rw [encC, assemble_length _ (wf c)]
  have hb₁ : (enc c.message).length ≤ 2658392 := enc_size_le c.message
  have hb₂ : (enc c.signature).length ≤ 2149634476 := enc_size_le c.signature
  rw [show fixedLen ((toParts c).map Prod.fst) = 8 from rfl,
      show varTotal (toParts c)
        = (enc c.message).length + ((enc c.signature).length + 0) from rfl]
  omega

end SignedBlock

instance : SSZCodec SignedBlock :=
  ⟨SignedBlock.encC, SignedBlock.decC, false, 2152292876⟩
instance : LawfulSSZ SignedBlock :=
  ⟨SignedBlock.decC_encC, SignedBlock.encC_size_le⟩
instance [Hasher] : HasHTR SignedBlock :=
  ⟨fun c => Merkle.merkleize [htr c.message, htr c.signature] none⟩

/-! ## BlocksByRootRequest -/

/-- Requested block roots, limit 2^10; fixed 32-byte elements (packed). -/
abbrev RequestedBlockRoots := SSZList Bytes32 1024

structure BlocksByRootRequest where
  roots : RequestedBlockRoots

namespace BlocksByRootRequest

def toParts (c : BlocksByRootRequest) : List Part := [varPart c.roots]

def schema : List (Option Nat) := [none]

def encC (c : BlocksByRootRequest) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError BlocksByRootRequest :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁] =>
    match dec (T := RequestedBlockRoots) s₁ with
    | .ok a => .ok ⟨a⟩
    | .error e => .error e
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : BlocksByRootRequest) : WFParts (toParts c) :=
  wfparts_cons_var _ wfparts_nil

theorem decC_encC (c : BlocksByRootRequest) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb : (enc c.roots).length ≤ 32768 := enc_size_le c.roots
    rw [show fixedLen ((toParts c).map Prod.fst) = 4 from rfl,
        show varTotal (toParts c) = (enc c.roots).length + 0 from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd = [enc c.roots] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]

theorem encC_size_le (c : BlocksByRootRequest) : (encC c).length ≤ 32772 := by
  rw [encC, assemble_length _ (wf c)]
  have hb : (enc c.roots).length ≤ 32768 := enc_size_le c.roots
  rw [show fixedLen ((toParts c).map Prod.fst) = 4 from rfl,
      show varTotal (toParts c) = (enc c.roots).length + 0 from rfl]
  omega

end BlocksByRootRequest

instance : SSZCodec BlocksByRootRequest :=
  ⟨BlocksByRootRequest.encC, BlocksByRootRequest.decC, false, 32772⟩
instance : LawfulSSZ BlocksByRootRequest :=
  ⟨BlocksByRootRequest.decC_encC, BlocksByRootRequest.encC_size_le⟩
instance [Hasher] : HasHTR BlocksByRootRequest :=
  ⟨fun c => Merkle.merkleize [htr c.roots] none⟩

/-! ## State -/

abbrev HistoricalBlockHashes := SSZList Bytes32 262144
abbrev JustifiedSlots := Bitlist 262144
abbrev Validators := SSZList Validator 4096
abbrev JustificationRoots := SSZList Bytes32 262144
abbrev JustificationValidators := Bitlist 1073741824

structure State where
  config : Config
  slot : Slot
  latestBlockHeader : BlockHeader
  latestJustified : Checkpoint
  latestFinalized : Checkpoint
  historicalBlockHashes : HistoricalBlockHashes
  justifiedSlots : JustifiedSlots
  validators : Validators
  justificationsRoots : JustificationRoots
  justificationsValidators : JustificationValidators

namespace State

def toParts (c : State) : List Part :=
  [fixedPart c.config, fixedPart c.slot, fixedPart c.latestBlockHeader,
   fixedPart c.latestJustified, fixedPart c.latestFinalized,
   varPart c.historicalBlockHashes, varPart c.justifiedSlots,
   varPart c.validators, varPart c.justificationsRoots,
   varPart c.justificationsValidators]

def schema : List (Option Nat) :=
  [some 8, some 8, some 112, some 40, some 40, none, none, none, none, none]

def encC (c : State) : List UInt8 := assemble (toParts c)

def decC (bs : List UInt8) : Except SSZError State :=
  match disassemble schema bs with
  | .error e => .error e
  | .ok [s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀] => do
    let config ← dec (T := Config) s₁
    let slot ← dec (T := Uint64) s₂
    let lbh ← dec (T := BlockHeader) s₃
    let lj ← dec (T := Checkpoint) s₄
    let lf ← dec (T := Checkpoint) s₅
    let hbh ← dec (T := HistoricalBlockHashes) s₆
    let js ← dec (T := JustifiedSlots) s₇
    let vs ← dec (T := Validators) s₈
    let jr ← dec (T := JustificationRoots) s₉
    let jv ← dec (T := JustificationValidators) s₁₀
    pure ⟨config, slot, lbh, lj, lf, hbh, js, vs, jr, jv⟩
  | .ok _ => .error (.invalidValue "internal: field count")

theorem wf (c : State) : WFParts (toParts c) :=
  wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_fixed _
    (wfparts_cons_fixed _ (wfparts_cons_fixed _ (wfparts_cons_var _
      (wfparts_cons_var _ (wfparts_cons_var _ (wfparts_cons_var _
        (wfparts_cons_var _ wfparts_nil)))))))))

theorem decC_encC (c : State) : decC (encC c) = .ok c := by
  have hasm := disassemble_assemble (toParts c) (wf c) (by
    have hb₁ : (enc c.historicalBlockHashes).length ≤ 8388608 :=
      enc_size_le c.historicalBlockHashes
    have hb₂ : (enc c.justifiedSlots).length ≤ 32769 :=
      enc_size_le c.justifiedSlots
    have hb₃ : (enc c.validators).length ≤ 458752 := enc_size_le c.validators
    have hb₄ : (enc c.justificationsRoots).length ≤ 8388608 :=
      enc_size_le c.justificationsRoots
    have hb₅ : (enc c.justificationsValidators).length ≤ 134217729 :=
      enc_size_le c.justificationsValidators
    rw [show fixedLen ((toParts c).map Prod.fst) = 228 from rfl,
        show varTotal (toParts c)
          = (enc c.historicalBlockHashes).length + ((enc c.justifiedSlots).length
            + ((enc c.validators).length + ((enc c.justificationsRoots).length
              + ((enc c.justificationsValidators).length + 0)))) from rfl]
    omega)
  have hsnd : (toParts c).map Prod.snd
      = [enc c.config, enc c.slot, enc c.latestBlockHeader,
         enc c.latestJustified, enc c.latestFinalized,
         enc c.historicalBlockHashes, enc c.justifiedSlots,
         enc c.validators, enc c.justificationsRoots,
         enc c.justificationsValidators] := rfl
  rw [hsnd] at hasm
  unfold decC encC
  rw [show schema = (toParts c).map Prod.fst from rfl]
  simp only [hasm, dec_enc]
  rfl

theorem encC_size_le (c : State) : (encC c).length ≤ 151486694 := by
  rw [encC, assemble_length _ (wf c)]
  have hb₁ : (enc c.historicalBlockHashes).length ≤ 8388608 :=
    enc_size_le c.historicalBlockHashes
  have hb₂ : (enc c.justifiedSlots).length ≤ 32769 :=
    enc_size_le c.justifiedSlots
  have hb₃ : (enc c.validators).length ≤ 458752 := enc_size_le c.validators
  have hb₄ : (enc c.justificationsRoots).length ≤ 8388608 :=
    enc_size_le c.justificationsRoots
  have hb₅ : (enc c.justificationsValidators).length ≤ 134217729 :=
    enc_size_le c.justificationsValidators
  rw [show fixedLen ((toParts c).map Prod.fst) = 228 from rfl,
      show varTotal (toParts c)
        = (enc c.historicalBlockHashes).length + ((enc c.justifiedSlots).length
          + ((enc c.validators).length + ((enc c.justificationsRoots).length
            + ((enc c.justificationsValidators).length + 0)))) from rfl]
  omega

end State

instance : SSZCodec State := ⟨State.encC, State.decC, false, 151486694⟩
instance : LawfulSSZ State := ⟨State.decC_encC, State.encC_size_le⟩
instance [Hasher] : HasHTR State :=
  ⟨fun c => Merkle.merkleize
    [htr c.config, htr c.slot, htr c.latestBlockHeader,
     htr c.latestJustified, htr c.latestFinalized,
     htr c.historicalBlockHashes, htr c.justifiedSlots,
     htr c.validators, htr c.justificationsRoots,
     htr c.justificationsValidators] none⟩

end Devnet
end LeanSSZ
