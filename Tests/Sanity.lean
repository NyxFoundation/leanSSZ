/-
FFI + merkleization sanity checks (known-answer tests).

Validates the C SHA-256 against NIST-derived known answers and the
merkleizer against the well-known Ethereum zero-subtree roots.
-/

import LeanSSZ

open LeanSSZ

def toHex (bs : ByteArray) : String :=
  String.join (bs.data.toList.map fun b =>
    let hex := "0123456789abcdef".toList
    String.mk [hex[(b.toNat / 16) % 16]!, hex[b.toNat % 16]!])

def check (name : String) (got expected : String) : IO Bool := do
  if got = expected then
    IO.println s!"ok   {name}"
    pure true
  else
    IO.println s!"FAIL {name}\n  got      {got}\n  expected {expected}"
    pure false

def main : IO UInt32 := do
  let mut allOk := true
  -- NIST: SHA-256 of the empty string
  let e ← check "sha256(empty)"
    (toHex (Sha256.hashRaw (ByteArray.mk #[])))
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  allOk := allOk && e
  -- NIST: SHA-256 of "abc"
  let abc ← check "sha256(abc)"
    (toHex (Sha256.hashRaw (String.toUTF8 "abc")))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  allOk := allOk && abc
  -- Ethereum zero-subtree roots: depth 1 = sha256(0^64)
  let z1 ← check "zeroHashes[1]"
    (toHex (Merkle.zeroHashes 1).val)
    "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
  allOk := allOk && z1
  let z2 ← check "zeroHashes[2]"
    (toHex (Merkle.zeroHashes 2).val)
    "db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71"
  allOk := allOk && z2
  -- hash_tree_root of Uint64 5: the 8 LE bytes zero-padded to one chunk
  let u ← check "htr(Uint64 5)"
    (toHex (htr (5 : Uint64)).val)
    "0500000000000000000000000000000000000000000000000000000000000000"
  allOk := allOk && u
  -- mix_in_length(zero root, 0): sha256(0^32 ++ 0^32) = zeroHashes[1]
  let m ← check "mixInLength(zero, 0)"
    (toHex (Merkle.mixInLength Merkle.zeroChunk 0).val)
    "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
  allOk := allOk && m
  if allOk then
    IO.println "all sanity checks passed"
    pure 0
  else
    pure 1
