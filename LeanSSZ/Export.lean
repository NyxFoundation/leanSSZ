/-
C ABI export layer (Verity C-8 seam pattern).

Byte-in / byte-out only: the proven Lean decoder is the authoritative
parser; nothing but `uint8*` + length crosses the boundary. Errors map to
small integer codes. Proofs are design-time artifacts — the caller links
the compiled functions and re-verifies nothing.

PoC surface: the `Block` container (fixed prefix + variable body — the
layout-stressing case). Extending to other containers is the same three
functions per type.
-/

import LeanSSZ.Devnet.ContainersVar
import LeanSSZ.Merkle.Root

namespace LeanSSZ.Export

open LeanSSZ LeanSSZ.Devnet

/-- `SSZError` over the wire: 0 = ok, 1 = length, 2 = value, 3 = offset. -/
def errCode : Except SSZError α → UInt16
  | .ok _ => 0
  | .error (.invalidLength ..) => 1
  | .error (.invalidValue _) => 2
  | .error (.invalidOffset _) => 3

/-- Strictly validate an SSZ `Block`. 0 = valid. -/
@[export lssz_block_validate]
def blockValidate (bs : ByteArray) : UInt16 :=
  errCode (deserialize (T := Block) bs)

/-- Decode then re-encode a `Block`; empty result = decode error.
By `deserialize_serialize` + `serialize_injective`, a non-empty result is
always byte-identical to a canonical input. -/
@[export lssz_block_reencode]
def blockReencode (bs : ByteArray) : ByteArray :=
  match deserialize (T := Block) bs with
  | .ok b => serialize b
  | .error _ => ByteArray.empty

/-- `hash_tree_root` of an SSZ-encoded `Block` (32 bytes); empty result =
decode error. -/
@[export lssz_block_htr]
def blockHtr (bs : ByteArray) : ByteArray :=
  match deserialize (T := Block) bs with
  | .ok b => (htr b).val
  | .error _ => ByteArray.empty

end LeanSSZ.Export
