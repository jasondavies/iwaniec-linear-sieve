import IwaniecLinearSieve.PrimeSums.Product
import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# Mertens' third theorem with the constant `e^{-γ}`

`R_asymp` gives `R z log z = c_R + O(pntE z)` for an unspecified constant `c_R > 0`. Mertens'
third theorem from PrimeNumberTheoremAnd (`Mertens.E₃.bound''`, vendored in
`vendor/strong-pnt`) identifies the limit: `c_R = e^{-γ}`.
-/

open Real Filter Topology Finset

namespace IwaniecLinearSieve

/-- The primes below `n + 1/2` are the primes `p ≤ n`. -/
theorem R_nat_add_half (n : ℕ) :
    R ((n : ℝ) + 1 / 2) =
      ∏ p ∈ Ioc 0 ⌊((n : ℝ) + 1 / 2)⌋₊ with p.Prime, (1 - (1 : ℝ) / p) := by
  have hfl : ⌊((n : ℝ) + 1 / 2)⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [hfl, R]
  refine prod_congr (Finset.ext fun p => ?_) fun p _ => by rw [one_div]
  rw [mem_primesLT, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hpn⟩
    refine ⟨⟨hp.pos, ?_⟩, hp⟩
    have : (p : ℝ) < n + 1 := by linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  · rintro ⟨⟨-, hpn⟩, hp⟩
    refine ⟨hp, ?_⟩
    have : (p : ℝ) ≤ n := by exact_mod_cast hpn
    linarith

/-- Mertens' third theorem in the form `R(n + 1/2) log (n + 1/2) → e^{-γ}`. -/
theorem tendsto_R_nat_add_half_mul_log :
    Tendsto (fun n : ℕ => R ((n : ℝ) + 1 / 2) * log ((n : ℝ) + 1 / 2)) atTop
      (𝓝 (exp (-eulerMascheroniConstant))) := by
  set P : ℝ → ℝ := fun x => ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p)
  have hP : Tendsto (fun x => P x * log x) atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
    have h := Mertens.E₃.bound''.mul (Asymptotics.IsEquivalent.refl (u := log))
    refine h.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop 1] with x hx
    have : log x ≠ 0 := (log_pos hx).ne'
    simp [this]
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (hP.comp hn).congr fun n => ?_
  simp only [Function.comp_apply, P, R_nat_add_half]

/-- The constant of `R_asymp` is `e^{-γ}`. -/
theorem eq_exp_neg_eulerMascheroniConstant_of_R {cR C : ℝ}
    (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ C * pntE z) :
    cR = exp (-eulerMascheroniConstant) := by
  refine tendsto_nhds_unique ?_ tendsto_R_nat_add_half_mul_log
  have hlim : Tendsto (fun z => R z * log z) atTop (𝓝 cR) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using tendsto_pntE.const_mul C)
    filter_upwards [eventually_ge_atTop 2] with z hz
    exact hR z hz
  exact hlim.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

/-- Mertens' third theorem: `R(z) log z → e^{-γ}`. -/
theorem tendsto_R_mul_log :
    Tendsto (fun z => R z * log z) atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  obtain ⟨cR, -, C, hC⟩ := R_asymp
  rw [← eq_exp_neg_eulerMascheroniConstant_of_R hC, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using tendsto_pntE.const_mul C)
  filter_upwards [eventually_ge_atTop 2] with z hz
  exact hC z hz

/-- `R_asymp` with the constant `e^{-γ}`:
`R(z) = e^{-γ} / log z + O(exp(-κ √log z) / log z)`. -/
theorem R_asymp_exp : ∃ C, ∀ z ≥ 2,
    |R z * log z - exp (-eulerMascheroniConstant)| ≤ C * pntE z := by
  obtain ⟨cR, -, C, hC⟩ := R_asymp
  exact ⟨C, eq_exp_neg_eulerMascheroniConstant_of_R hC ▸ hC⟩

end IwaniecLinearSieve
