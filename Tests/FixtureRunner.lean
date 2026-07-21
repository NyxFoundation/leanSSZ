/-
leanSpec devnet SSZ fixture conformance runner.

Fixtures: vendored from a local leanSpec working tree at commit
4c9d640de090b2a1caf0782ff965b321450389b1 (fixtures are generated, not
committed upstream). Each case carries the JSON `value` and the reference
`serialized` hex.

Checks per case:
  1. encode: `enc (parse value) == serialized`;
  2. decode: `enc <$> dec serialized == ok serialized` (with 1 and the
     proven injectivity, this pins the decoded value to the original).

hash_tree_root is NOT covered by these fixtures (they carry no root
field); it is validated by `lake exe sanity` known answers only.
-/

import LeanSSZ
import Lean.Data.Json

open Lean (Json)
open LeanSSZ LeanSSZ.Devnet

abbrev P := Except String

/-! ## Primitive parsers -/

def hexNib (c : Char) : P Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error s!"bad hex char {c}"

def hexToBytes (s : String) : P (List UInt8) := do
  let body : String := if s.startsWith "0x" then (s.drop 2).toString else s
  let cs := body.toList
  if cs.length % 2 ≠ 0 then throw "odd hex length"
  let rec go : List Char → P (List UInt8)
    | [] => .ok []
    | hi :: lo :: rest => do
      let h ← hexNib hi
      let l ← hexNib lo
      let tl ← go rest
      pure (UInt8.ofNat (h * 16 + l) :: tl)
    | _ => .error "odd hex length"
  go cs

def jField (j : Json) (k : String) : P Json := j.getObjVal? k

def pNat (j : Json) : P Nat := j.getNat?

def pU64 (j : Json) : P Uint64 := do
  let n ← pNat j
  if n < 2 ^ 64 then pure (UInt64.ofNat n) else throw "uint64 out of range"

def pBytesN (n : Nat) (j : Json) : P (BytesN n) := do
  let s ← j.getStr?
  let bs ← hexToBytes s
  if h : bs.length = n then
    pure ⟨⟨bs.toArray⟩, by simpa [ByteArray.size] using h⟩
  else throw s!"expected {n} bytes, got {bs.length}"

def pFp (j : Json) : P Fp := do
  let n ← pNat j
  if h : n < fpP then
    pure ⟨UInt32.ofNat n, by
      have h32 : n < 2 ^ 32 := by
        have : fpP < 2 ^ 32 := by decide
        omega
      simpa [UInt32.toNat_ofNat_of_lt' h32] using h⟩
  else throw "Fp out of range"

def pDataArray (j : Json) : P (Array Json) := do
  (← jField j "data").getArr?

def pBoolList (j : Json) : P (List Bool) := do
  let arr ← pDataArray j
  arr.toList.mapM (·.getBool?)

def pBitlist (limit : Nat) (j : Json) : P (Bitlist limit) := do
  let bits ← pBoolList j
  if h : bits.length ≤ limit then pure ⟨bits, h⟩
  else throw "bitlist over limit"

def pSSZList {T : Type} (limit : Nat) (pe : Json → P T) (j : Json) :
    P (SSZList T limit) := do
  let arr ← pDataArray j
  let xs ← arr.toList.mapM pe
  if h : xs.length ≤ limit then pure ⟨xs, h⟩
  else throw "list over limit"

def pVector {T : Type} (n : Nat) (pe : Json → P T) (j : Json) :
    P (SSZVector T n) := do
  let arr ← pDataArray j
  let xs ← arr.toList.mapM pe
  if h : xs.toArray.size = n then pure ⟨xs.toArray, h⟩
  else throw s!"vector length mismatch"

/-! ## Container parsers (field order = fixture JSON order) -/

def pCheckpoint (j : Json) : P Checkpoint := do
  pure ⟨← pBytesN 32 (← jField j "root"), ← pU64 (← jField j "slot")⟩

def pAttestationData (j : Json) : P AttestationData := do
  pure ⟨← pU64 (← jField j "slot"), ← pCheckpoint (← jField j "head"),
        ← pCheckpoint (← jField j "target"), ← pCheckpoint (← jField j "source")⟩

def pAttestation (j : Json) : P Attestation := do
  pure ⟨← pU64 (← jField j "validatorId"),
        ← pAttestationData (← jField j "data")⟩

def pSignedAttestation (j : Json) : P SignedAttestation := do
  pure ⟨← pU64 (← jField j "validatorId"),
        ← pAttestationData (← jField j "data"),
        ← pBytesN 424 (← jField j "signature")⟩

def pValidator (j : Json) : P Validator := do
  pure ⟨← pBytesN 52 (← jField j "attestationPubkey"),
        ← pBytesN 52 (← jField j "proposalPubkey"),
        ← pU64 (← jField j "index")⟩

def pConfig (j : Json) : P Config := do
  pure ⟨← pU64 (← jField j "genesisTime")⟩

def pBlockHeader (j : Json) : P BlockHeader := do
  pure ⟨← pU64 (← jField j "slot"), ← pU64 (← jField j "proposerIndex"),
        ← pBytesN 32 (← jField j "parentRoot"),
        ← pBytesN 32 (← jField j "stateRoot"),
        ← pBytesN 32 (← jField j "bodyRoot")⟩

def pStatus (j : Json) : P Status := do
  pure ⟨← pCheckpoint (← jField j "finalized"), ← pCheckpoint (← jField j "head")⟩

def pPublicKey (j : Json) : P PublicKey := do
  pure ⟨← pVector 8 pFp (← jField j "root"),
        ← pVector 5 pFp (← jField j "parameter")⟩

def pAggregatedAttestation (j : Json) : P AggregatedAttestation := do
  pure ⟨← pBitlist 4096 (← jField j "aggregationBits"),
        ← pAttestationData (← jField j "data")⟩

def pBlockBody (j : Json) : P BlockBody := do
  pure ⟨← pSSZList 4096 pAggregatedAttestation (← jField j "attestations")⟩

def pBlock (j : Json) : P Block := do
  pure ⟨← pU64 (← jField j "slot"), ← pU64 (← jField j "proposerIndex"),
        ← pBytesN 32 (← jField j "parentRoot"),
        ← pBytesN 32 (← jField j "stateRoot"),
        ← pBlockBody (← jField j "body")⟩

def pByteList512 (j : Json) : P ByteList512KiB := do
  let s ← (← jField j "data").getStr?
  let bs ← hexToBytes s
  if h : bs.length ≤ 512 * 1024 then pure ⟨bs, h⟩
  else throw "bytelist over limit"

def pAggregatedSignatureProof (j : Json) : P AggregatedSignatureProof := do
  pure ⟨← pBitlist 4096 (← jField j "participants"),
        ← pByteList512 (← jField j "proofData")⟩

def pBlockSignatures (j : Json) : P BlockSignatures := do
  pure ⟨← pSSZList 4096 pAggregatedSignatureProof (← jField j "attestationSignatures"),
        ← pBytesN 424 (← jField j "proposerSignature")⟩

def pSignedBlock (j : Json) : P SignedBlock := do
  pure ⟨← pBlock (← jField j "message"),
        ← pBlockSignatures (← jField j "signature")⟩

def pBlocksByRootRequest (j : Json) : P BlocksByRootRequest := do
  pure ⟨← pSSZList 1024 (pBytesN 32) (← jField j "roots")⟩

def pState (j : Json) : P State := do
  pure ⟨← pConfig (← jField j "config"), ← pU64 (← jField j "slot"),
        ← pBlockHeader (← jField j "latestBlockHeader"),
        ← pCheckpoint (← jField j "latestJustified"),
        ← pCheckpoint (← jField j "latestFinalized"),
        ← pSSZList 262144 (pBytesN 32) (← jField j "historicalBlockHashes"),
        ← pBitlist 262144 (← jField j "justifiedSlots"),
        ← pSSZList 4096 pValidator (← jField j "validators"),
        ← pSSZList 262144 (pBytesN 32) (← jField j "justificationsRoots"),
        ← pBitlist 1073741824 (← jField j "justificationsValidators")⟩

/-! ## Case runner -/

def runCase {T : Type} [SSZCodec T] (pv : Json → P T)
    (val : Json) (ser : List UInt8) : Option String :=
  match pv val with
  | .error e => some s!"value parse: {e}"
  | .ok v =>
    if enc v ≠ ser then
      some "encode mismatch"
    else
      match dec (T := T) ser with
      | .error _ => some "decode failed"
      | .ok v' =>
        if enc v' ≠ ser then some "decode/re-encode mismatch" else none

def dispatch (typeName : String) (val : Json) (ser : List UInt8) :
    Option String :=
  match typeName with
  | "Checkpoint" => runCase pCheckpoint val ser
  | "AttestationData" => runCase pAttestationData val ser
  | "Attestation" => runCase pAttestation val ser
  | "SignedAttestation" => runCase pSignedAttestation val ser
  | "Validator" => runCase pValidator val ser
  | "Config" => runCase pConfig val ser
  | "BlockHeader" => runCase pBlockHeader val ser
  | "Status" => runCase pStatus val ser
  | "PublicKey" => runCase pPublicKey val ser
  | "Signature" => runCase (pBytesN 424) val ser
  | "AggregatedAttestation" => runCase pAggregatedAttestation val ser
  | "BlockBody" => runCase pBlockBody val ser
  | "Block" => runCase pBlock val ser
  | "BlockSignatures" => runCase pBlockSignatures val ser
  | "SignedBlock" => runCase pSignedBlock val ser
  | "BlocksByRootRequest" => runCase pBlocksByRootRequest val ser
  | "AggregatedSignatureProof" => runCase pAggregatedSignatureProof val ser
  | "State" => runCase pState val ser
  | _ => some s!"unknown type {typeName}"

def main : IO UInt32 := do
  let root : System.FilePath := "Tests/fixtures"
  let files ← root.walkDir
  let mut pass := 0
  let mut fail := 0
  for f in files do
    if f.extension = some "json" then
      let text ← IO.FS.readFile f
      match Json.parse text with
      | .error e => IO.println s!"FAIL {f}: json parse {e}"; fail := fail + 1
      | .ok top =>
        let entries := top.getObj?.toOption.map (·.toArray) |>.getD #[]
        for ⟨caseName, body⟩ in entries do
          let result : P (Option String) := do
            let tn ← (← jField body "typeName").getStr?
            let val ← jField body "value"
            let serHex ← (← jField body "serialized").getStr?
            let ser ← hexToBytes serHex
            pure (dispatch tn val ser)
          match result with
          | .error e => IO.println s!"FAIL {caseName}: {e}"; fail := fail + 1
          | .ok (some msg) => IO.println s!"FAIL {caseName}: {msg}"; fail := fail + 1
          | .ok none => pass := pass + 1
  IO.println s!"fixtures: {pass} passed, {fail} failed"
  pure (if fail = 0 then 0 else 1)
