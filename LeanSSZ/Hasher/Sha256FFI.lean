/-
SHA-256 via C FFI — the ONLY trust commitments in this library.

Per the leanSSZ hashing policy (docs/DESIGN.md): the hash function is not
implemented in Lean. The C implementation (`c/sha256.c`) is validated
behaviourally (NIST CAVP vectors, leanSpec fixtures); its contract enters
the proof world as the named axiom below. Each `@[extern]` is replaceable
later by a `@[csimp]`-proved pure implementation, and the axiom by a
proved theorem, without changing dependent statements.

Everything an auditor must trust is in THIS file (plus SSZ-7 collision
resistance in `Merkle/Root.lean`). Recover the inventory with:

  grep -rEn '^axiom |^@\[extern' LeanSSZ/ --include='*.lean'
-/

import LeanSSZ.Core.Bytes

namespace LeanSSZ
namespace Sha256

/-- `sha256(a ++ b)` for two 32-byte inputs — the sole merkleization
primitive (leaf packing needs no hashing; `mix_in_length` is a combine). -/
@[extern "lssz_sha256_combine"]
opaque combineRaw (a b : @& ByteArray) : ByteArray

/-- General SHA-256, exposed for CAVP validation in the test suite. -/
@[extern "lssz_sha256"]
opaque hashRaw (data : @& ByteArray) : ByteArray

/-- Trust commitment: the FFI combine returns 32 bytes. Behaviourally
checked by the test suite; replaceable by a theorem once a pure
implementation lands. -/
axiom combineRaw_size : ∀ a b : ByteArray, (combineRaw a b).size = 32

/-- Typed merkleization combine. -/
def combine (a b : Bytes32) : Bytes32 :=
  ⟨combineRaw a.val b.val, combineRaw_size ..⟩

end Sha256

/-- The hash backing merkleization. One field because SSZ merkleization
only ever hashes 64-byte concatenations. Swap point for a future
post-quantum hasher (R6). -/
class Hasher where
  combine : Bytes32 → Bytes32 → Bytes32

instance : Hasher := ⟨Sha256.combine⟩

end LeanSSZ
