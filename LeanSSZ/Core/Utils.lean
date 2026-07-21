/-
SSZ power-of-two ceiling helper.

Mirrors `_next_pow2` in `src/lean_spec/spec/crypto/merkleization.py`:

  def _next_pow2(x: int) -> int:
      if x <= 1:
          return 1
      return 1 << (x - 1).bit_length()

Pads Merkle-tree leaf counts up to the next power of two.

Migrated from formal-leanSpec `LeanSpec/SSZ/Utils.lean` (discharges SSZ-6
of the proposition catalog).
-/

namespace LeanSSZ

/-- Smallest power of two greater than or equal to `x`. Returns 1 for `x ≤ 1`. -/
def getPowerOfTwoCeil (x : Nat) : Nat :=
  if x ≤ 1 then 1 else 2 ^ ((x - 1).log2 + 1)

/--
SSZ-6: `getPowerOfTwoCeil x` is a power of two `2 ^ k` with `x ≤ 2 ^ k`,
and it is minimal — either `k = 0` or `2 ^ (k - 1) < x`.
-/
theorem ceil_pow2_minimal (x : Nat) (_h : 0 < x) :
    x ≤ getPowerOfTwoCeil x ∧
      ∃ k, getPowerOfTwoCeil x = 2 ^ k ∧ (k = 0 ∨ 2 ^ (k - 1) < x) := by
  unfold getPowerOfTwoCeil
  by_cases hx : x ≤ 1
  · rw [if_pos hx]
    exact ⟨hx, 0, rfl, Or.inl rfl⟩
  · rw [if_neg hx]
    have hne : x - 1 ≠ 0 := by omega
    have h_upper : x - 1 < 2 ^ ((x - 1).log2 + 1) := Nat.lt_log2_self
    have h_lower : 2 ^ (x - 1).log2 ≤ x - 1 := Nat.log2_self_le hne
    refine ⟨by omega, (x - 1).log2 + 1, rfl, Or.inr ?_⟩
    rw [Nat.add_sub_cancel]
    omega

end LeanSSZ
