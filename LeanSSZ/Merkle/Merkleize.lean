/-
SSZ merkleization primitives.

Mirrors `src/lean_spec/spec/crypto/merkleization.py` in leanSpec:
  - `chunkify`: right-pad serialized bytes to 32-byte chunks;
  - `merkleize chunks limit`: Merkle root over chunks, tree width padded
    to the next power of two of the limit (or the chunk count), missing
    subtrees filled with cached zero-subtree roots;
  - `mixInLength`: `H(root ++ uint256_LE(length))` for variable-length
    types.

Executable layer: the proof scope of this library is serialization
(roundtrip / injectivity / size); hash-related properties are trust
commitments (see `Hasher/Sha256FFI.lean` and SSZ-7 in `Merkle/Root.lean`).
-/

import LeanSSZ.Core.Basic
import LeanSSZ.Core.Uint
import LeanSSZ.Core.Utils
import LeanSSZ.Hasher.Sha256FFI

namespace LeanSSZ
namespace Merkle

/-- All-zero 32-byte chunk. -/
def zeroChunk : Bytes32 := BytesN.zero 32

/-- Root of the all-zero perfect subtree of depth `d`. -/
def zeroHashes [Hasher] : Nat → Bytes32
  | 0 => zeroChunk
  | d + 1 => Hasher.combine (zeroHashes d) (zeroHashes d)

/-- Right-pad `bytes` to a 32-byte boundary and split into chunks. -/
def chunkify : List UInt8 → List Bytes32
  | [] => []
  | bytes@(_ :: _) =>
    let head := bytes.take 32
    let chunk : Bytes32 :=
      ⟨⟨(head ++ List.replicate (32 - head.length) 0).toArray⟩, by
        simp [ByteArray.size]
        have : head.length ≤ 32 := by
          simp only [head, List.length_take]
          omega
        omega⟩
    chunk :: chunkify (bytes.drop 32)
  termination_by bytes => bytes.length
  decreasing_by
    subst bytes
    simp [List.length_drop]
    omega

/-- One pairing round: combine adjacent chunks, an odd tail pairs with the
zero subtree of the current depth. -/
def pairUp [Hasher] : List Bytes32 → Bytes32 → List Bytes32
  | [], _ => []
  | [l], z => [Hasher.combine l z]
  | l :: r :: rest, z => Hasher.combine l r :: pairUp rest z

/-- Run `rounds` pairing rounds, tracking the zero-subtree depth. -/
def rounds [Hasher] : List Bytes32 → Nat → Nat → List Bytes32
  | level, _, 0 => level
  | level, d, r + 1 => rounds (pairUp level (zeroHashes d)) (d + 1) r

/-- Tree depth for a target leaf capacity: `2 ^ depth` is the padded
width (`getPowerOfTwoCeil`). -/
def depthFor (x : Nat) : Nat :=
  if x ≤ 1 then 0 else (x - 1).log2 + 1

/-- SSZ Merkle root over `chunks`, with tree width from `limit` when
given (list/bitlist capacity) or the chunk count (vectors, containers).
Precondition (maintained by every caller): `chunks.length ≤ limit`. -/
def merkleize [Hasher] (chunks : List Bytes32) (limit : Option Nat) : Bytes32 :=
  let target := match limit with
    | some l => l
    | none => chunks.length
  let k := depthFor target
  (rounds chunks 0 k).headD (zeroHashes k)

/-- `H(root ++ uint256_LE(length))` — disambiguates lists by length. -/
def mixInLength [Hasher] (root : Bytes32) (length : Nat) : Bytes32 :=
  Hasher.combine root ⟨⟨(LE.encodeNat length 32).toArray⟩, by
    simp [ByteArray.size, LE.encodeNat_length]⟩

/-- Chunk count of a `len`-byte payload. -/
def chunkCount (len : Nat) : Nat := (len + 31) / 32

end Merkle
end LeanSSZ
