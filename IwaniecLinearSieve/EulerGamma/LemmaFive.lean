import IwaniecLinearSieve.EulerGamma.Buchstab
import IwaniecLinearSieve.SieveFunctions.LemmaFive

/-!
# [I71, Lemma 5]: `F(3) = 2e^γ - 3`, and `ω(u) → e^{-γ}`

`SieveFunctions.LemmaFive` proves `f(s) = s - (F(3) + 3) log (s - 1)` on `[2, 4]` and `f(2) = 2`.
Here we complete [I71, Lemma 5] following Iwaniec. Let `A = F(3) + 3` and extend
`W = f - F` (on `s ≥ 3`) to `ℝ` by

* `W(s) = s W'(s+1) = f(s) - F(3) - 3 + s` on `[2, 3]`,
* `W(s) = s W'(s+1) = 2s - A` on `(-∞, 2]` (`WSieve`).

Then `W'(s) = W(s-1)/(s-1)` for `s > 2` (`hasDerivAt_WSieve`; first for `s ≠ 3, 4`, then at
`3` and `4` by continuity of the right-hand side),
so `w(s) = (2s - W(s))/(s A)` satisfies `w(s) = 1/s` on `[1, 2]` and `(s w(s))' = w(s - 1)` for
`s > 2`: `w` is Buchstab's function `ω` (`buchstab_eq_wSieve`). Since `W(s) = O(s e^{-s})`,
`ω(s) - 2/A = O(e^{-s})`, so by `eq_exp_neg_of_integrableOn_buchstab_sub` `2/A = e^{-γ}`, i.e.
`F(3) = 2e^γ - 3` (`FSieve_three`), and `ω(u) → e^{-γ}` (`tendsto_buchstab`). Consequences:

* `fSieve_eq_of_mem_Icc`: `f(s) = s - 2e^γ log(s - 1)` for `2 ≤ s ≤ 4`;
* `FSieve_eq_of_mem_Icc`: `F(s) = 2e^γ (1 + ∫_1^{s-2} log x/(x+1) dx) - s` for `3 ≤ s ≤ 5`
  ([I71] prints `s - 6 + 2e^γ (1 - ∫_1^{s-2} …)`, which has the wrong sign: `F` decreases);
* `MSieve_eq_of_mem_Icc` (the Corollary): `M(s) = 2e^γ (1 - log(s - 1))` for `2 ≤ s ≤ 3`.
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- Iwaniec's `W`, extended to `ℝ`: `f(s) - F(s) - (3 - s)⁺` for `s ≥ 2`, `2s - (F(3) + 3)` for
`s ≤ 2`. -/
noncomputable def WSieve (s : ℝ) : ℝ :=
  if s ≤ 2 then 2 * s - (FSieve 3 + 3) else fSieve s - FSieve s - max (3 - s) 0

/-- Iwaniec's `w(s) = (2s - W(s)) / (s (3 + F(3)))`. -/
noncomputable def wSieve (s : ℝ) : ℝ := (2 * s - WSieve s) / (s * (FSieve 3 + 3))

theorem FSieve_three_add_three_pos : 0 < FSieve 3 + 3 := by
  linarith [FSieve_nonneg 3]

theorem WSieve_of_le_two {s : ℝ} (hs : s ≤ 2) : WSieve s = 2 * s - (FSieve 3 + 3) := by
  rw [WSieve, ite_eq_left hs]

theorem WSieve_of_two_le {s : ℝ} (hs : 2 ≤ s) :
    WSieve s = fSieve s - FSieve s - max (3 - s) 0 := by
  rcases hs.lt_or_eq with hs | rfl
  · rw [WSieve, ite_eq_right (not_le.2 hs)]
  · rw [WSieve, ite_eq_left le_rfl, fSieve_two, FSieve_of_le_three (s := 2) (by norm_num)]
    norm_num
    ring

theorem WSieve_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    WSieve s = 2 * s - (FSieve 3 + 3) - (FSieve 3 + 3) * log (s - 1) := by
  rw [WSieve_of_two_le hs.1, fSieve_eq_on_Icc ⟨hs.1, by linarith [hs.2]⟩,
    FSieve_of_le_three hs.2, max_eq_left (by linarith [hs.2])]
  ring

theorem WSieve_of_three_le {s : ℝ} (hs : 3 ≤ s) : WSieve s = fSieve s - FSieve s := by
  rw [WSieve_of_two_le (by linarith), max_eq_right (by linarith), sub_zero]

theorem continuous_WSieve : Continuous WSieve := by
  refine Continuous.if_le (by fun_prop) ((continuous_fSieve.sub continuous_FSieve).sub
    (by fun_prop)) continuous_id continuous_const fun s hs => ?_
  have := WSieve_of_two_le (le_of_eq hs.symm)
  rw [WSieve_of_le_two hs.le] at this
  exact this

/-- [I71, (3.8)] for the extended `W`: `W'(s) = W(s-1)/(s-1)` for `s > 2`, `s ≠ 3, 4`. -/
theorem hasDerivAt_WSieve_of_ne {s : ℝ} (hs : 2 < s) (hs3 : s ≠ 3) (hs4 : s ≠ 4) :
    HasDerivAt WSieve (WSieve (s - 1) / (s - 1)) s := by
  have hs1 : s - 1 ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hs3 with h3 | h3
  · -- `2 < s < 3`
    have hd : HasDerivAt (fun u => 2 * u - (FSieve 3 + 3) - (FSieve 3 + 3) * log (u - 1))
        (2 - (FSieve 3 + 3) / (s - 1)) s := by
      have := (((hasDerivAt_id' s).const_mul 2).sub_const (FSieve 3 + 3)).sub
        (((hasDerivAt_id' s).sub_const 1).log hs1 |>.const_mul (FSieve 3 + 3))
      convert this using 1
      field_simp
    have hd' := hd.congr_of_eventuallyEq (f₁ := WSieve) (by
      filter_upwards [Ioo_mem_nhds hs h3] with u hu
      exact WSieve_of_mem_Icc ⟨hu.1.le, hu.2.le⟩)
    convert hd' using 1
    rw [WSieve_of_le_two (by linarith)]
    field_simp
  rcases lt_or_gt_of_ne hs4 with h4 | h4
  · -- `3 < s < 4`
    have hd := (hasDerivAt_fSieve_of_lt_four hs h4).sub (hasDerivAt_FSieve h3)
    have hd' := hd.congr_of_eventuallyEq (f₁ := WSieve) (by
      filter_upwards [Ioi_mem_nhds h3] with u hu
      exact WSieve_of_three_le (le_of_lt hu))
    convert hd' using 1
    rw [WSieve_of_mem_Icc ⟨by linarith, by linarith⟩,
      fSieve_eq_on_Icc ⟨by linarith, by linarith⟩]
    field_simp
    ring
  · -- `s > 4`
    have hd := (hasDerivAt_fSieve_of_four_lt h4).sub (hasDerivAt_FSieve h3)
    have hd' := hd.congr_of_eventuallyEq (f₁ := WSieve) (by
      filter_upwards [Ioi_mem_nhds h3] with u hu
      exact WSieve_of_three_le (le_of_lt hu))
    convert hd' using 1
    rw [WSieve_of_three_le (by linarith)]
    field_simp
    ring

theorem continuousOn_WSieve_shift :
    ContinuousOn (fun t => WSieve (t - 1) / (t - 1)) (Ioi 2) :=
  (continuous_WSieve.comp (continuous_sub_right 1)).continuousOn.div
    (continuous_sub_right 1).continuousOn fun t ht => by linarith [mem_Ioi.1 ht]

/-- [I71, (3.8)] for the extended `W` (Iwaniec: `W` is of class `C¹` on `s ≥ 2`):
`W'(s) = W(s-1)/(s-1)` for `s > 2`. -/
theorem hasDerivAt_WSieve {s : ℝ} (hs : 2 < s) :
    HasDerivAt WSieve (WSieve (s - 1) / (s - 1)) s := by
  have hc := continuousOn_WSieve_shift
  -- `W(y) = W(s) + ∫_s^y W(t-1)/(t-1) dt` for `y > 2`
  have heq : ∀ y ∈ Ioi (2 : ℝ),
      WSieve y = WSieve s + ∫ t in s..y, WSieve (t - 1) / (t - 1) := by
    intro y hy
    have hsub : uIcc s y ⊆ Ioi 2 := by
      intro t ht
      rw [mem_uIcc] at ht
      simp only [mem_Ioi] at hy ⊢
      rcases ht with ht | ht <;> linarith [ht.1]
    have := integral_eq_of_hasDerivAt_off_countable (f := WSieve)
      (f' := fun t => WSieve (t - 1) / (t - 1)) (s := {3, 4}) (Set.toFinite _).countable
      continuous_WSieve.continuousOn (fun t ht => by
        simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at ht
        refine hasDerivAt_WSieve_of_ne ?_ ht.2.1 ht.2.2
        have := ht.1.1
        rw [min_lt_iff] at this
        simp only [mem_Ioi] at hy
        rcases this with h | h <;> linarith)
      ((hc.mono hsub).intervalIntegrable)
    linarith
  have hF : HasDerivAt (fun y => WSieve s + ∫ t in s..y, WSieve (t - 1) / (t - 1))
      (WSieve (s - 1) / (s - 1)) s :=
    (intervalIntegral.integral_hasDerivAt_right
      ((hc.mono fun t ht => by
        rw [uIcc_self, mem_singleton_iff] at ht
        exact ht ▸ hs).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter isOpen_Ioi s hs)
      (hc.continuousAt (Ioi_mem_nhds hs))).const_add _
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  exact heq y hy

/-- [I71, (3.8)]: `W = f - F` satisfies `W'(s) = W(s-1)/(s-1)` for `s ≥ 4`. -/
theorem hasDerivAt_fSieve_sub_FSieve {s : ℝ} (hs : 4 ≤ s) :
    HasDerivAt (fun s => fSieve s - FSieve s)
      ((fSieve (s - 1) - FSieve (s - 1)) / (s - 1)) s := by
  rw [← WSieve_of_three_le (by linarith)]
  refine (hasDerivAt_WSieve (by linarith)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (show (3 : ℝ) < s by linarith)] with u hu
  exact (WSieve_of_three_le (le_of_lt hu)).symm

theorem wSieve_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) : wSieve s = 1 / s := by
  have hs0 : s ≠ 0 := by linarith [hs.1]
  rw [wSieve, WSieve_of_le_two hs.2]
  field_simp [FSieve_three_add_three_pos.ne']
  ring

theorem continuousOn_wSieve : ContinuousOn wSieve (Ici 1) :=
  ((continuous_const.mul continuous_id).sub continuous_WSieve).continuousOn.div
    (continuous_id.mul continuous_const).continuousOn fun s hs =>
      mul_ne_zero (by linarith [hs.out]) FSieve_three_add_three_pos.ne'

theorem hasDerivAt_mul_wSieve {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun u => u * wSieve u) (wSieve (s - 1)) s := by
  have hA : FSieve 3 + 3 ≠ 0 := FSieve_three_add_three_pos.ne'
  have hd := (((hasDerivAt_id' s).const_mul 2).sub (hasDerivAt_WSieve hs)).div_const
    (FSieve 3 + 3)
  have hd' := hd.congr_of_eventuallyEq (f₁ := fun u => u * wSieve u) (by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < s by linarith)] with u hu
    have hu0 : u ≠ 0 := (mem_Ioi.1 hu).ne'
    simp only [wSieve, Pi.sub_apply]
    field_simp)
  convert hd' using 1
  have hs1 : s - 1 ≠ 0 := by linarith
  simp only [wSieve]
  field_simp

/-- [I71, Lemma 5]: Iwaniec's `w` is Buchstab's function `ω` on `[1, ∞)`. -/
theorem wSieve_eqOn_buchstab : EqOn wSieve buchstab (Ici 1) :=
  eqOn_buchstab (S := ∅) countable_empty continuousOn_wSieve
    (fun _ hu => wSieve_of_mem_Icc hu) fun _ hu _ => hasDerivAt_mul_wSieve hu

theorem buchstab_eq_wSieve {u : ℝ} (hu : 1 ≤ u) :
    buchstab u = (2 * u - WSieve u) / (u * (FSieve 3 + 3)) :=
  (wSieve_eqOn_buchstab (mem_Ici.2 hu)).symm

/-- `ω(u) - 2/(F(3) + 3) = O(e^{-u})`. -/
theorem exists_abs_buchstab_sub_le :
    ∃ C, ∀ u ≥ 3, |buchstab u - 2 / (FSieve 3 + 3)| ≤ C * exp (-u) := by
  have hA : 0 < FSieve 3 + 3 := FSieve_three_add_three_pos
  refine ⟨(gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) / (FSieve 3 + 3),
    fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have h : buchstab u - 2 / (FSieve 3 + 3) = -(WSieve u / (u * (FSieve 3 + 3))) := by
    rw [buchstab_eq_wSieve (by linarith)]
    field_simp
    ring
  have hW : |WSieve u| ≤ fSieve u + FSieve u := by
    rw [WSieve_of_three_le hu, abs_le]
    constructor <;> linarith [fSieve_nonneg u, FSieve_nonneg u]
  rw [h, abs_neg, abs_div, abs_of_pos (by positivity : 0 < u * (FSieve 3 + 3)),
    div_le_iff₀ (by positivity)]
  calc |WSieve u| ≤ fSieve u + FSieve u := hW
    _ ≤ gLead * (1 - gRatio)⁻¹ * u * exp (-u) +
        gLead * (exp 1 / 3) * (1 - gRatio)⁻¹ * u * exp (-u) :=
        add_le_add (fSieve_le (by linarith)) (FSieve_le (by linarith))
    _ = _ := by field_simp

/-- [I71, Lemma 5]: `F(3) + 3 = 2e^γ` (via `ω(∞) = e^{-γ}`). -/
theorem FSieve_three_add_three : FSieve 3 + 3 = 2 * exp eulerMascheroniConstant := by
  set A := FSieve 3 + 3
  have hA : 0 < A := FSieve_three_add_three_pos
  obtain ⟨C, hC⟩ := exists_abs_buchstab_sub_le
  have hint : IntegrableOn (fun u => buchstab u - 2 / A) (Ioi 1) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 3 by norm_num)]
    refine IntegrableOn.union ?_ ?_
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      exact (continuousOn_buchstab.mono fun u hu => by
        simp only [mem_Ioi]; linarith [hu.1]).sub continuousOn_const
    · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 3 one_pos).const_mul C)
        (measurable_buchstab.sub_const _).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 3 < u)
      rw [Real.norm_eq_abs]
      simpa using hC u hu.le
  have h := eq_exp_neg_of_integrableOn_buchstab_sub hint
  rw [div_eq_iff hA.ne', exp_neg] at h
  field_simp at h
  linarith

/-- [I71, Lemma 5]: `F(3) = 2e^γ - 3`. -/
theorem FSieve_three : FSieve 3 = 2 * exp eulerMascheroniConstant - 3 := by
  linarith [FSieve_three_add_three]

/-- de Bruijn's theorem `ω(u) → e^{-γ}` ([I71] quotes it from Jurkat–Richert), with an
exponential rate. -/
theorem exists_abs_buchstab_sub_exp_le :
    ∃ C, ∀ u ≥ 3, |buchstab u - exp (-eulerMascheroniConstant)| ≤ C * exp (-u) := by
  obtain ⟨C, hC⟩ := exists_abs_buchstab_sub_le
  refine ⟨C, fun u hu => ?_⟩
  have := hC u hu
  rwa [FSieve_three_add_three, show 2 / (2 * exp eulerMascheroniConstant) =
    exp (-eulerMascheroniConstant) by rw [exp_neg]; field_simp] at this

/-- de Bruijn's theorem: Buchstab's function tends to `e^{-γ}`. -/
theorem tendsto_buchstab : Tendsto buchstab atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  obtain ⟨C, hC⟩ := exists_abs_buchstab_sub_exp_le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  filter_upwards [eventually_ge_atTop 3] with u hu
  exact hC u hu

/-- [I71, Lemma 5]: `f(s) = s - 2e^γ log (s - 1)` for `2 ≤ s ≤ 4`. -/
theorem fSieve_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    fSieve s = s - 2 * exp eulerMascheroniConstant * log (s - 1) := by
  rw [fSieve_eq_on_Icc hs, FSieve_three_add_three]

/-- [I71, Corollary to Lemma 5]: `M(s) = 2e^γ (1 - log (s - 1))` for `2 ≤ s ≤ 3`. -/
theorem MSieve_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    MSieve s = 2 * exp eulerMascheroniConstant * (1 - log (s - 1)) := by
  rw [MSieve_of_le_three hs.2, fSieve_eq_of_mem_Icc ⟨hs.1, by linarith [hs.2]⟩, FSieve_three]
  ring

/-- `x ↦ ∫_1^x log t / (t + 1) dt` has derivative `log x / (x + 1)` for `x > 0`. -/
theorem hasDerivAt_integral_log_div {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, log t / (t + 1)) (log x / (x + 1)) x := by
  have hc : ContinuousOn (fun t => log t / (t + 1)) (Ioi 0) :=
    (continuousOn_log.mono fun _ ht => (mem_Ioi.1 ht).ne').div (by fun_prop) fun t ht => by
      linarith [mem_Ioi.1 ht]
  refine intervalIntegral.integral_hasDerivAt_right ?_
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))
  refine (hc.mono fun t ht => ?_).intervalIntegrable
  rw [mem_uIcc] at ht
  simp only [mem_Ioi]
  rcases ht with ht | ht <;> linarith [ht.1]

/-- [I71, Lemma 5]: `F(s) = 2e^γ (1 + ∫_1^{s-2} log x / (x + 1) dx) - s` for `3 ≤ s ≤ 5`.
([I71] prints `s - 6 + 2e^γ (1 - ∫_1^{s-2} …)`; differentiating `F(s) = ∫_s^∞ f(t-1)/(t-1) dt`
gives the formula here, and `F` is decreasing.) -/
theorem FSieve_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 5) :
    FSieve s = 2 * exp eulerMascheroniConstant *
      (1 + ∫ x in (1 : ℝ)..(s - 2), log x / (x + 1)) - s := by
  set c := 2 * exp eulerMascheroniConstant
  set G : ℝ → ℝ := fun t => c * (1 + ∫ x in (1 : ℝ)..(t - 2), log x / (x + 1)) - t
  have hG : ∀ t, 2 < t → HasDerivAt G (c * (log (t - 2) / (t - 2 + 1)) - 1) t := fun t ht => by
    have h1 := (hasDerivAt_integral_log_div (by linarith : 0 < t - 2)).comp t
      ((hasDerivAt_id' t).sub_const 2)
    rw [mul_one] at h1
    exact ((h1.const_add 1).const_mul c).sub (hasDerivAt_id' t)
  have hcont : ContinuousOn (fun t => FSieve t - G t) (Icc 3 s) :=
    continuous_FSieve.continuousOn.sub fun t ht =>
      (hG t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioo 3 s, HasDerivAt (fun t => FSieve t - G t) 0 t := by
    intro t ht
    have h := (hasDerivAt_FSieve ht.1).sub (hG t (by linarith [ht.1]))
    convert h using 1
    rw [fSieve_eq_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2, hs.2]⟩]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    rw [show t - 1 - 1 = t - 2 by ring, show t - 2 + 1 = t - 1 by ring]
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hcont hderiv
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  have h3 : FSieve 3 - G 3 = 0 := by
    simp only [G, FSieve_three, c]
    norm_num
  linarith

end IwaniecLinearSieve
