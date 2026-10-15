import IwaniecJacobsthal.LinearSieve.TheoremFourAux

/-!
# Real-analysis facts for large `y` in [I71, Theorem 4]

With `L = log y`, `ℓ = log log 3y`, `Λ = log log y`, `ξ = ξ(y) = L / ℓ^{11/5}` and
`w = y^{1/ξ}` (so `log w = ℓ^{11/5}` and `pntE w = exp (-κ ℓ^{11/10})`):

* `eventually_delta_mul_le`: `δ(s₀, y) (1 + C ξ² pntE w) ≤ 1 + Λ² / (8 L²)` ([I71, (4.6)]);
* `eventually_mul_pntE_le`: `K ξ² L³ pntE w ≤ 1` ([I71, (4.2), (4.3)]);
* `eventually_crude`: the crude bound `2 (e X/(ξ-2))^{ξ-2}` for the depth sums at `w`
  (with `X = log log w + C'`) times `L⁴` is below the Lemma 9 lower bound for `G(ξ/2)` and below
  `δ(ξ/2, y)` times the Lemma 9 lower bound for `G(ξ)` ([I71, (4.4), (4.5), (4.9), (4.10)]).
-/

open Real Set Filter Topology MeasureTheory Finset

namespace IwaniecJacobsthal.TheoremFour

theorem eventually_one_le_loglog : ∀ᶠ y : ℝ in atTop, 1 ≤ log (log y) := by
  sorry

theorem eventually_delta_mul_le (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ y : ℝ in atTop,
    delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) ≤
      1 + log (log y) ^ 2 / (8 * log y ^ 2) := by
  sorry

theorem eventually_mul_pntE_le (K : ℝ) : ∀ᶠ y : ℝ in atTop,
    K * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y)) ≤ 1 := by
  sorry

theorem eventually_crude (c C' : ℝ) (hc : 0 ≤ c) (hC' : 1 ≤ C') : ∀ᶠ y : ℝ in atTop,
    0 < log (log (y ^ (1 / xi y))) + C' ∧
    2 * exp 1 * (log (log (y ^ (1 / xi y))) + C') ≤ xi y - 2 ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      exp (-(xi y / 2 * log (xi y / 2)) - xi y / 2 * log (log (xi y / 2)) - c * (xi y / 2)) ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      delta (xi y / 2) y * exp (-(xi y * log (xi y)) - xi y * log (log (xi y)) - c * xi y) := by
  sorry

end IwaniecJacobsthal.TheoremFour
