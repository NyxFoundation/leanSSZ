/-
SSZ fixed-length Vector primitive.

Mirrors `src/lean_spec/spec/ssz/collections.py` (`SSZVector`) in leanSpec:
a fixed-length homogeneous sequence of exactly `n` elements. Length is
carried in the type, as with `BytesN`.

Migrated from formal-leanSpec `LeanSpec/SSZ/Vector.lean` (discharges SSZ-5
of the proposition catalog).

The `SSZType` instance (element-wise serialization of fixed-size element
types, and offset-table serialization of variable-size ones) lands with the
container machinery — see docs/DESIGN.md, Phase 1/2.
-/

import LeanSSZ.Core.Basic

namespace LeanSSZ

/-- A fixed-length SSZ vector of `n` elements of type `T`. The length
invariant `data.size = n` is carried by the structure. -/
structure SSZVector (T : Type) (n : Nat) where
  data : Array T
  size_eq : data.size = n

namespace SSZVector

instance {T : Type} {n : Nat} [Inhabited T] : Inhabited (SSZVector T n) :=
  ⟨⟨Array.replicate n default, by simp⟩⟩

@[inline] def size {T : Type} {n : Nat} (v : SSZVector T n) : Nat := v.data.size

/-- SSZ-5: a fixed-length vector always holds exactly `n` elements. -/
theorem sszvector_length {T : Type} {n : Nat} (v : SSZVector T n) :
    v.data.size = n := v.size_eq

end SSZVector
end LeanSSZ
