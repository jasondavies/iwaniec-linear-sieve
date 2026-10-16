import IwaniecLinearSieve.Jacobsthal.Reduction

/-!
# Jacobsthal's problem ([I78])

Iwaniec's application of the linear sieve: if `m` consecutive integers are each divisible by one
of `r ≥ 2` given primes, then `m ≪ (r log r)²`. The shifted sieve ([I78, Lemma 1],
`Jacobsthal/ShiftedSieve.lean`) transfers the Rosser weights for the first `r` primes to any `r`
primes; `Jacobsthal/Reduction.lean` combines it with `linearSieveEstimate`.

The rest of [I78] (Lemma 1 in full, Lemma 2, the Theorem, and the Corollary deduced from it) is in
`Jacobsthal/LemmaOne.lean`, `Jacobsthal/LemmaTwo.lean` and `Jacobsthal/Theorem.lean`, which this
module does not import.
-/

namespace IwaniecLinearSieve

/-- **Iwaniec's theorem** ([I78, Corollary]): if `m` consecutive integers are each divisible by
one of `r ≥ 2` given primes, then `m ≪ (r log r)²`. -/
theorem iwaniecBound :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 :=
  iwaniecBound_of_estimates linearSieveEstimate R_lower nth_prime_le

end IwaniecLinearSieve
