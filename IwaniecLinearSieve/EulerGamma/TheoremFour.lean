module

public import IwaniecLinearSieve.EulerGamma.Mertens
public import IwaniecLinearSieve.LinearSieve.TheoremFour

@[expose] public section

/-!
# [I71, Theorem 4] in Iwaniec's normalisation

`theorem4` holds for any constant `c_R` with `R(z) log z = c_R + O(pntE z)`; by Mertens' third
theorem (`R_asymp_exp`) we may take `c_R = e^{-γ}`, which gives Iwaniec's form
`e^γ Q_{r,y}(s) ≤ f_r(s)/log y + c₇ r/(r+1) δ(s, y) G_r(s)/log² y`.
-/

open Real

namespace IwaniecLinearSieve

/-- [I71, Theorem 4] (main terms), for `k = 1`, in Iwaniec's normalisation: there is `c₇ ≥ 0`
such that for all `r`, both sieves, `y > 1` and `sMin lower ≤ s ≤ ξ(y)`,

`e^γ · fail lower r y (y^{1/s}) ≤ M(s)/L + c₇ r/(r+1) δ(s, y) G(s)/L²`,

where `M = mainMaj lower` (`f`, resp. `F + (3 - s)⁺`), `G = errMaj lower` (`𝔣`, resp. `𝔉`),
`L = log y`. -/
theorem theorem4_exp :
    ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
      s ≤ xi y → exp eulerMascheroniConstant * fail lower r y (y ^ (1 / s)) ≤
        mainMaj lower s / log y +
          c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2 := by
  obtain ⟨C, hC⟩ := R_asymp_exp
  obtain ⟨c₇, hc₇, h⟩ := theorem4 (exp_pos _) hC
  refine ⟨c₇, hc₇, fun r lower y s hy hs hsξ => ?_⟩
  have := mul_le_mul_of_nonneg_left (h r lower y s hy hs hsξ) (exp_pos eulerMascheroniConstant).le
  rwa [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at this

end IwaniecLinearSieve
