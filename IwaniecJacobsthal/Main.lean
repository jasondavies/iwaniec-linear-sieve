import IwaniecJacobsthal.Jacobsthal
import IwaniecJacobsthal.PrimeSums

/-! # Iwaniec's bound, reduced to the linear sieve estimate -/

namespace IwaniecJacobsthal

/-- Iwaniec's bound for Jacobsthal's problem, given the linear sieve estimate at level
`C₀ z²` ([I71, Theorems 4–5], [I78, Lemma 2]). -/
theorem iwaniecBound_of_linearSieveEstimate (h : LinearSieveEstimate) :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 :=
  iwaniecBound_of_estimates h R_lower nth_prime_le

end IwaniecJacobsthal
