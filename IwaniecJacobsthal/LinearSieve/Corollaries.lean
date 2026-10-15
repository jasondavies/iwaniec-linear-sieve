import IwaniecJacobsthal.LinearSieve.LemmaEleven
import IwaniecJacobsthal.Rosser
import IwaniecJacobsthal.PrimeSums

/-!
# [I71, Corollaries 1 and 3 to Lemma 13]

With `L = log y` and `t_p = L / log p`, so that the inner level of the recursion at `p` is
`(y/p, p)` with parameter `t_p - 1` (`log (y/p) = log p · (t_p - 1)`).

* `lemma13_param`: Lemma 13 in the variable `t = L / log u`: for `F ≥ 0` antitone on `[α, β]`,
  `|∑_{y^{1/β} ≤ p ≤ y^{1/α}} F(t_p)/p - ∫_α^β F(t)/t dt| ≤ C F(α) pntE(y^{1/β})`
  (substitution `u = e^{L/t}` in `lemma13_mono_of_subset`).
* `cor1`: Corollary 1, for the primes `y^{1/β} ≤ p < y^{1/α}` and any `M ≥ 0` antitone on
  `[α - 1, β - 1]`.
* `cor3`: Corollary 3, for the primes `y^{1/b} ≤ p` in `rosserPrimes lower y (y^{1/s})`
  (the primes of the recursion), uniformly in `sMin lower ≤ s`, with `s₀ = e^{32}` and the upper
  limit `ξ` replaced by any `b ≥ s₀` with `160 b² log⁴ b ≤ L²` and `y^{1/b} ≥ 2`.
-/

open Real Set Filter Topology MeasureTheory Finset

namespace IwaniecJacobsthal

/-! ### Lemma 13 in the variable `t = log y / log u` -/

theorem integral_comp_log_div {F : ℝ → ℝ} {y α β : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ u in y ^ (1 / β)..y ^ (1 / α), F (log y / log u) / (u * log u) =
      ∫ t in α..β, F t / t := by
  set L := log y
  have hL : 0 < L := log_pos hy
  have hy0 : 0 < y := by linarith
  set f : ℝ → ℝ := fun t => exp (L * t⁻¹)
  set f' : ℝ → ℝ := fun t => exp (L * t⁻¹) * (L * -(t ^ 2)⁻¹)
  have hpos : ∀ x ∈ uIcc α β, 0 < x := fun x hx => by
    rw [uIcc_of_le hαβ] at hx; linarith [hx.1]
  have hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x := fun x hx =>
    ((hasDerivAt_inv hx.ne').const_mul L).exp
  have hfA : ∀ γ, f γ = y ^ (1 / γ) := fun γ => by
    simp only [f]; rw [rpow_def_of_pos hy0, one_div]
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := α) (b := β) (f := f)
    (f' := f') (g := fun u => F (L / log u) / (u * log u))
    (continuousOn_of_forall_continuousAt fun x hx => (hderiv x (hpos x hx)).continuousAt)
    (fun x hx => hderiv x (by
      rw [min_eq_left hαβ] at hx; linarith [hx.1]))
    (fun x hx => by
      simp only [f']
      rw [mul_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
        (neg_nonpos.2 (mul_nonneg hL.le (by positivity))))
  rw [hfA, hfA, intervalIntegral.integral_symm (y ^ (1 / β)) (y ^ (1 / α))] at h
  have hcongr : ∫ x in α..β, ((fun u => F (L / log u) / (u * log u)) ∘ f) x * f' x =
      ∫ x in α..β, -(F x / x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := hpos x hx
    simp only [Function.comp, f, f', log_exp]
    have : L / (L * x⁻¹) = x := by field_simp
    rw [this]
    have := exp_pos (L * x⁻¹)
    field_simp
  rw [hcongr, intervalIntegral.integral_neg, neg_inj] at h
  exact h.symm

theorem log_rpow_one_div {y : ℝ} (hy : 0 < y) (γ : ℝ) : log (y ^ (1 / γ)) = log y / γ := by
  rw [log_rpow hy]; ring

/-- For `u ∈ [y^{1/β}, y^{1/α}]`, `log y / log u ∈ [α, β]`. -/
theorem div_log_mem_Icc {y α β u : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β)
    (hu : u ∈ Icc (y ^ (1 / β)) (y ^ (1 / α))) : 0 < log u ∧ log y / log u ∈ Icc α β := by
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hβ : 0 < β := hα.trans_le hαβ
  have hB0 : 0 < y ^ (1 / β) := rpow_pos_of_pos hy0 _
  have hu0 : 0 < u := hB0.trans_le hu.1
  have h1 : log y / β ≤ log u := log_rpow_one_div hy0 β ▸ log_le_log hB0 hu.1
  have h2 : log u ≤ log y / α := log_rpow_one_div hy0 α ▸ log_le_log hu0 hu.2
  have hlu : 0 < log u := (div_pos hL hβ).trans_le h1
  refine ⟨hlu, ?_, ?_⟩
  · rw [le_div_iff₀ hlu]; rw [le_div_iff₀ hα] at h2; linarith
  · rw [div_le_iff₀ hlu]; rw [div_le_iff₀ hβ] at h1; linarith

/-- [I71, Lemma 13] in the variable `t = log y / log u`: for `F ≥ 0` antitone on `[α, β]`, and any
set `S` of primes between those in `(y^{1/β}, y^{1/α})` and those in `[y^{1/β}, y^{1/α}]`,
`|∑_{p ∈ S} F(t_p)/p - ∫_α^β F(t)/t dt| ≤ C F(α) pntE(y^{1/β})`. -/
theorem lemma13_param : ∃ C, 0 ≤ C ∧ ∀ (F : ℝ → ℝ) (y α β : ℝ) (S : Finset ℕ), 1 < y → 0 < α →
    α ≤ β → 2 ≤ y ^ (1 / β) → AntitoneOn F (Icc α β) → (∀ t ∈ Icc α β, 0 ≤ F t) →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / β) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / α)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / β) < p → (p : ℝ) < y ^ (1 / α) → p ∈ S) →
    |∑ p ∈ S, F (log y / log p) / p - ∫ t in α..β, F t / t| ≤ C * F α * pntE (y ^ (1 / β)) := by
  obtain ⟨C, hC0, hC⟩ := lemma13_mono_of_subset
  refine ⟨C, hC0, fun F y α β S hy hα hαβ hB hF hF0 hS1 hS2 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hBA : y ^ (1 / β) ≤ y ^ (1 / α) :=
    rpow_le_rpow_of_exponent_le hy.le (one_div_le_one_div_of_le hα hαβ)
  have hmono : MonotoneOn (fun u => F (log y / log u)) (Icc (y ^ (1 / β)) (y ^ (1 / α))) := by
    intro u hu v hv huv
    obtain ⟨hlu, hmu⟩ := div_log_mem_Icc hy hα hαβ hu
    obtain ⟨hlv, hmv⟩ := div_log_mem_Icc hy hα hαβ hv
    exact hF hmv hmu (div_le_div_of_nonneg_left hL.le hlu
      (log_le_log (by linarith [hu.1]) huv))
  have h := hC (fun u => F (log y / log u)) (y ^ (1 / α)) (y ^ (1 / β)) S hB hBA hmono
    (fun u hu => hF0 _ (div_log_mem_Icc hy hα hαβ hu).2) hS1 hS2
  rwa [integral_comp_log_div hy hα hαβ, log_rpow_one_div hy0, div_div_cancel₀ hL.ne'] at h

/-! ### Corollary 1 -/

theorem log_div_prime_eq {y : ℝ} {p : ℕ} (hy : 0 < y) (hp : 1 < p) :
    log (y / p) = log p * (log y / log p - 1) := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  rw [log_div hy.ne' (by positivity), mul_sub, mul_div_cancel₀ _ hlp.ne', mul_one]

/-- `log y / log p ≥ α` for `p ≤ y^{1/α}`. -/
theorem le_div_log_of_le_rpow {y α : ℝ} {p : ℕ} (hy : 1 < y) (hα : 0 < α) (hp : 1 < p)
    (hpA : (p : ℝ) ≤ y ^ (1 / α)) : α ≤ log y / log p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := log_le_log (by positivity) hpA
  rw [log_rpow_one_div (by linarith)] at h
  rw [le_div_iff₀ hlp]; rw [le_div_iff₀ hα] at h; linarith

theorem antitoneOn_div_sub_one : AntitoneOn (fun t : ℝ => t / (t - 1)) (Ioi 1) := by
  intro u hu v hv huv
  have hu1 : 0 < u - 1 := by linarith [hu.out]
  have hv1 : 0 < v - 1 := by linarith [hv.out]
  simp only
  rw [div_le_div_iff₀ hv1 hu1]; nlinarith

/-- [I71, Corollary 1 to Lemma 13]: for `M ≥ 0` antitone on `[α - 1, β - 1]`, `2 ≤ α ≤ β`,
`y^{1/β} ≥ 2`,
`|∑_{y^{1/β} ≤ p < y^{1/α}} M(t_p - 1)/(p log (y/p)) - L⁻¹ ∫_α^β M(t-1)/(t-1) dt|
  ≤ C M(α - 1) pntE(y^{1/β}) / L`. -/
theorem cor1 : ∃ C, 0 ≤ C ∧ ∀ (M : ℝ → ℝ) (y α β : ℝ), 1 < y → 2 ≤ α → α ≤ β →
    2 ≤ y ^ (1 / β) → AntitoneOn M (Icc (α - 1) (β - 1)) → (∀ t ∈ Icc (α - 1) (β - 1), 0 ≤ M t) →
    |∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
        M (log y / log p - 1) / (p * log (y / p)) -
      (∫ t in α..β, M (t - 1) / (t - 1)) / log y| ≤
      C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by
  obtain ⟨C, hC0, hC⟩ := lemma13_param
  refine ⟨2 * C, by linarith, fun M y α β hy hα hαβ hB hM hM0 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  set F : ℝ → ℝ := fun t => M (t - 1) * (t / (t - 1)) / log y with hFdef
  have hMt : AntitoneOn (fun t => M (t - 1)) (Icc α β) := fun u hu v hv huv =>
    hM ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1], by linarith [hv.2]⟩
      (by linarith)
  have hF : AntitoneOn F (Icc α β) := by
    have := antitoneOn_mul_of_nonneg hMt (antitoneOn_div_sub_one.mono fun t ht =>
      show (1 : ℝ) < t by linarith [ht.1])
      (fun t ht => hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      fun t ht => div_nonneg (by linarith [ht.1]) (by linarith [ht.1])
    exact fun u hu v hv huv => div_le_div_of_nonneg_right (this hu hv huv) hL.le
  have hF0 : ∀ t ∈ Icc α β, 0 ≤ F t := fun t ht =>
    div_nonneg (mul_nonneg (hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (div_nonneg (by linarith [ht.1]) (by linarith [ht.1]))) hL.le
  have h := hC F y α β ((primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p)) hy
    (by linarith) hαβ hB hF hF0
    (fun p hp => by
      rw [mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1, hp.2, hp.1.2.le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, mem_primesLT]; exact ⟨⟨hp, h2⟩, h1.le⟩)
  have hsum : ∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
      F (log y / log p) / p = ∑ p ∈ (primesLT (y ^ (1 / α))).filter
        (fun p : ℕ => y ^ (1 / β) ≤ p), M (log y / log p - 1) / (p * log (y / p)) := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter, mem_primesLT] at hp
    have hp1 := hp.1.1.one_lt
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp1)
    have ht := le_div_log_of_le_rpow hy (by linarith) hp1 hp.1.2.le
    have ht1 : 0 < log y / log p - 1 := by linarith
    rw [log_div_prime_eq hy0 hp1]
    simp only [F]
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
  have hint : ∫ t in α..β, F t / t = (∫ t in α..β, M (t - 1) / (t - 1)) / log y := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hαβ] at ht
    have : 0 < t := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [F]
    field_simp
  have hFα : F α ≤ 2 * M (α - 1) / log y := by
    have hMα := hM0 (α - 1) ⟨le_rfl, by linarith⟩
    have : α / (α - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    simp only [F]
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  rw [hsum, hint] at h
  refine h.trans ?_
  calc C * F α * pntE (y ^ (1 / β)) ≤ C * (2 * M (α - 1) / log y) * pntE (y ^ (1 / β)) := by
        have := pntE_pos (y ^ (1 / β))
        gcongr
    _ = 2 * C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by ring

end IwaniecJacobsthal
