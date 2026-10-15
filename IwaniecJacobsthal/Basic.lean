import Mathlib

/-!
# Shared notation

Iwaniec works with primes below a real bound `z`. For `p : ℕ` and `z : ℝ` we have `p < z` iff
`p < ⌈z⌉₊`, so the primes below `z` are `Nat.primesBelow ⌈z⌉₊`.
-/

open Real

namespace IwaniecJacobsthal

/-- The primes `p < z`. -/
noncomputable def primesLT (z : ℝ) : Finset ℕ := Nat.primesBelow ⌈z⌉₊

/-- `P(z) = ∏_{p < z} p`. -/
noncomputable def primorialLT (z : ℝ) : ℕ := ∏ p ∈ primesLT z, p

/-- Iwaniec's `R(z) = ∏_{p < z} (1 - 1/p)` (his `R_k` with `k = 1`). -/
noncomputable def R (z : ℝ) : ℝ := ∏ p ∈ primesLT z, (1 - (p : ℝ)⁻¹)

theorem mem_primesLT {z : ℝ} {p : ℕ} : p ∈ primesLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  simp [primesLT, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

end IwaniecJacobsthal
