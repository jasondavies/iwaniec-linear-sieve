import IwaniecJacobsthal.SieveMajorants.Majorants

/-!
# [I71, Lemmas 8, 9 (lower bound), 10]

* Lemma 8: `𝔐(s-1) < 4 s² 𝔐(s)` for `s ≥ 3`.
* Lemma 10: `log t 𝔐(t) < 2 t/(t-1)² 𝔐(t-1)` for `t ≥ 2`; hence `𝔐(t) t log t / 𝔐(t-1) < 9/2`
  for `t ≥ 3`, and the Corollary `G_{r+1}(t) (t-1)² log t / (G_r(t-1) t) < 4` for `t ≥ 2`.
* Lemma 9 (lower bound): `G_r(s) ≥ exp(-s log s - s log log s - c s)` for `s ≥ 3`.

[I71] proves Lemma 10 assuming that `𝔐(t-1)/𝔐(t)` is increasing; we instead use a first
crossing argument for the inequality itself (cf. [Opera de Cribro, Lemma 11.7]). For Lemma 9 we
compare `𝔐` with the explicit subsolution `exp(-(s log s + s log log s + 2s))` of (3.12),
instead of quoting the asymptotics of Hua's book.
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecJacobsthal

/-! ### Lemma 8 -/

/-- From (3.12): `𝔐(s - 1/2) ≤ 2(s-1)²/s 𝔐(s)` for `s ≥ 3`. -/
theorem bigM_sub_half_le {s : ℝ} (hs : 3 ≤ s) :
    bigM (s - 1 / 2) ≤ 2 * (s - 1) ^ 2 / s * bigM s := by
  have hs0 : 0 < s := by linarith
  have hy : 0 < (s - 1) ^ 2 := by nlinarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have hwc := continuousOn_weight_mul continuous_bigM (a := s - 1) (b := s) (by linarith)
  have hI : ∀ a b, s - 1 ≤ a → a ≤ b → b ≤ s →
      IntervalIntegrable (fun x => (1 - 1 / (2 * x ^ 2)) * bigM x) volume a b :=
    fun a b ha hab hb => (hwc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI (s - 1) (s - 1 / 2) le_rfl (by linarith) (by linarith))
    (hI (s - 1 / 2) s (by linarith) (by linarith) le_rfl)
  have h2 : 0 ≤ ∫ x in (s - 1 / 2)..s, (1 - 1 / (2 * x ^ 2)) * bigM x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx =>
      (mul_pos (weight_mem (by linarith [hx.1])).1 (bigM_pos x)).le
  have h1 : ∫ _ in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2) ≤
      ∫ x in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hI _ _ le_rfl (by linarith) (by linarith)) fun x hx => ?_
    have hw : 1 - 1 / (2 * (s - 1) ^ 2) ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [hx.1])
      linarith
    exact mul_le_mul hw (bigM_antitone hx.2) (bigM_pos _).le
      (weight_mem (by linarith [hx.1])).1.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have key := bigM_integral_identity hs
  rw [← hsplit] at key
  have : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) ≤
      ((s - 1) ^ 2 - 1 / 2) * bigM s / s := by linarith
  have e1 : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) =
      ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1 / 2) / (2 * (s - 1) ^ 2) := by
    field_simp; ring
  rw [e1, div_le_div_iff₀ (by positivity) hs0] at this
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
  nlinarith

/-- [I71, Lemma 8]: `𝔐(s-1) < 4 s² 𝔐(s)` for `s ≥ 3`. -/
theorem bigM_sub_one_lt {s : ℝ} (hs : 3 ≤ s) : bigM (s - 1) < 4 * s ^ 2 * bigM s := by
  have hs0 : 0 < s := by linarith
  have hB := bigM_sub_half_le hs
  have hMs := bigM_pos s
  rcases le_total s (7 / 2) with h | h
  · have h1 : bigM (s - 1) ≤ 3 := bigM_le_three _
    have h2 : bigM 3 ≤ bigM (s - 1 / 2) := bigM_antitone (by linarith)
    rw [bigM_three] at h2
    have h3 : 2 * (s - 1) ^ 2 / s ≤ s ^ 2 := by
      rw [div_le_iff₀ hs0]; nlinarith
    have := mul_le_mul_of_nonneg_right h3 hMs.le
    nlinarith [log_two_lt_d9]
  · have hA := bigM_sub_half_le (s := s - 1 / 2) (by linarith)
    rw [show s - 1 / 2 - 1 / 2 = s - 1 by ring] at hA
    have h3 : 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) < 2 * s := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have h4 : 2 * (s - 1) ^ 2 / s < 2 * s := by
      rw [div_lt_iff₀ hs0]; nlinarith
    have h5 : 0 < 2 * (s - 1) ^ 2 / s := div_pos (by nlinarith) hs0
    calc bigM (s - 1) ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * bigM (s - 1 / 2) := hA
      _ ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * (2 * (s - 1) ^ 2 / s * bigM s) :=
        mul_le_mul_of_nonneg_left hB (div_nonneg (by positivity) (by linarith))
      _ < 2 * s * (2 * s * bigM s) := by
        apply mul_lt_mul' h3.le (mul_lt_mul_of_pos_right h4 hMs) (by positivity) (by linarith)
      _ = 4 * s ^ 2 * bigM s := by ring

/-- [I71, Lemma 8] in ratio form. -/
theorem bigM_sub_one_div_lt {s : ℝ} (hs : 3 ≤ s) : bigM (s - 1) / bigM s < 4 * s ^ 2 := by
  rw [div_lt_iff₀ (bigM_pos s)]; exact bigM_sub_one_lt hs

/-! ### Lemma 10 -/

/-- `∫_{a}^{a+1} exp(-λ(x - a)) dx = (1 - exp(-λ))/λ`. -/
theorem integral_exp_neg_mul_unit (a : ℝ) {l : ℝ} (hl : l ≠ 0) :
    ∫ x in a..(a + 1), exp (-(l * (x - a))) = (1 - exp (-l)) / l := by
  have hderiv : ∀ x ∈ uIcc a (a + 1), HasDerivAt (fun x => -exp (-(l * (x - a))) / l)
      (exp (-(l * (x - a)))) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).sub_const a).const_mul l).neg).exp.neg.div_const l
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x => exp (-(l * (x - a)))).intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, mul_one, sub_self, mul_zero, neg_zero, exp_zero]
  ring

theorem log_four_lt : log 4 < 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  have := log_two_lt_d9
  push_cast
  linarith

/-- The inequality behind [I71, Lemma 10]: `log t · 𝔐(t) < 2 t/(t-1)² · 𝔐(t-1)` for
`t ≥ 2`. -/
theorem log_mul_bigM_lt {t : ℝ} (ht : 2 ≤ t) :
    log t * bigM t < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := by
  refine sub_pos.1 <| pos_of_first_crossing
    (f := fun t => 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t) (a₀ := 2) (a := 2)
    ?_ ?_ ?_ ?_ t ht
  · refine ContinuousOn.sub (ContinuousOn.mul (continuousOn_const.mul
      (continuousOn_id.div ((continuousOn_id.sub continuousOn_const).pow 2) fun x hx => ?_))
      (continuous_bigM.comp (continuous_sub_right 1)).continuousOn)
      ((continuousOn_log.mono fun x hx => ?_).mul continuous_bigM.continuousOn)
    · have : 0 < x - 1 := by linarith [hx.out]
      positivity
    · simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.out]
  · intro x hx
    obtain rfl : x = 2 := le_antisymm hx.2 hx.1
    rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith [log_two_lt_d9]
  · rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith [log_two_lt_d9]
  intro t ht _ hpos
  show 0 < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t
  rw [sub_pos]
  have ht0 : 0 < t := by linarith
  have hB := bigM_pos (t - 1)
  have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
  rcases le_total t 3 with h3 | h3
  · -- explicit range `2 < t ≤ 3`
    rw [bigM_of_le_two (show t - 1 ≤ 2 by linarith)]
    have hl : log t < 1.3863 := (log_le_log ht0 (by linarith)).trans_lt log_four_lt
    have hk : 3 / 4 ≤ t / (t - 1) ^ 2 := by
      rw [le_div_iff₀ (by have : 0 < t - 1 := by linarith
                          positivity)]
      nlinarith
    have := bigM_le_three t
    nlinarith
  rcases le_total t 4 with h4 | h4
  · -- crude range `3 ≤ t ≤ 4`, from `𝔐(t) ≤ t/((t-1)² - 1/2) 𝔐(t-1)`
    have hl : log t < 1.3863 := (log_le_log ht0 h4).trans_lt log_four_lt
    have hR := bigM_le_ratio h3
    have hy : 4 ≤ (t - 1) ^ 2 := by nlinarith
    have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by linarith
    have key : log t * (t / ((t - 1) ^ 2 - 1 / 2)) < 2 * (t / (t - 1) ^ 2) := by
      rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hr (by linarith)]
      have : 1 < (2 - log t) * (t - 1) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left this ht0]
    calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * bigM (t - 1)) :=
          mul_le_mul_of_nonneg_left hR hlog0
      _ = log t * (t / ((t - 1) ^ 2 - 1 / 2)) * bigM (t - 1) := by ring
      _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB
  -- main range `t > 4`
  set L₁ := log (t - 1) with hL₁
  set l := L₁ / 2 with hl
  have hL₁1 : 1 < L₁ := by
    rw [hL₁, lt_log_iff_exp_lt (by linarith)]
    linarith [exp_one_lt_d9]
  have hl0 : 0 < l := by linarith
  -- `𝔐(x) ≤ 𝔐(t-1) exp(-l(x - (t-1)))` on `[t-1, t]`
  have hanti : AntitoneOn (fun x => bigM x * exp (l * x)) (Icc (t - 1) t) := by
    have hd : ∀ x, 3 < x → HasDerivAt (fun x => bigM x * exp (l * x))
        (-(x / (x - 1) ^ 2 * bigM (x - 1)) * exp (l * x) + bigM x * (exp (l * x) * l)) x :=
      fun x hx => (hasDerivAt_bigM hx).mul (((hasDerivAt_id x).const_mul l).exp.congr_deriv
        (by simp))
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuous_bigM.mul (continuous_const.mul continuous_id).rexp).continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact (hd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · rw [(hd x (by linarith [hx.1])).deriv]
      have hfx := hpos x ⟨by linarith [hx.1], hx.2⟩
      have hlx : L₁ ≤ log x := log_le_log (by linarith) hx.1.le
      have hMx := bigM_pos x
      have : l * bigM x < x / (x - 1) ^ 2 * bigM (x - 1) := by nlinarith
      have he := exp_pos (l * x)
      nlinarith
  have hbound : ∀ x ∈ Icc (t - 1) t,
      (1 - 1 / (2 * x ^ 2)) * bigM x ≤ bigM (t - 1) * exp (-(l * (x - (t - 1)))) := by
    intro x hx
    have h := hanti ⟨le_rfl, by linarith⟩ hx hx.1
    simp only at h
    have hw := weight_mem (x := x) (by linarith [hx.1])
    have hMx := bigM_pos x
    have e : bigM (t - 1) * exp (-(l * (x - (t - 1)))) =
        bigM (t - 1) * exp (l * (t - 1)) / exp (l * x) := by
      rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]; ring_nf
    rw [e, le_div_iff₀ (exp_pos _)]
    calc (1 - 1 / (2 * x ^ 2)) * bigM x * exp (l * x) ≤ 1 * bigM x * exp (l * x) := by
          gcongr; exact hw.2
      _ ≤ _ := by rw [one_mul]; exact h
  have hint : ((t - 1) ^ 2 - 1 / 2) * bigM t / t ≤ bigM (t - 1) * ((1 - exp (-l)) / l) := by
    rw [bigM_integral_identity h3, ← integral_exp_neg_mul_unit (t - 1) hl0.ne',
      sub_add_cancel, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) ((by fun_prop : Continuous fun x =>
          bigM (t - 1) * exp (-(l * (x - (t - 1))))).intervalIntegrable _ _) hbound
  -- the numerical inequality, with `q = exp l = √(t-1)`
  set q := exp l with hq
  have hq2 : q ^ 2 = t - 1 := by
    rw [hq, sq, ← exp_add, show l + l = L₁ by rw [hl]; ring, hL₁, exp_log (by linarith)]
  have hq1 : 1 < q := one_lt_exp_iff.2 hl0
  have hel : exp (-l) = q⁻¹ := by rw [exp_neg]
  have hLt : log t ≤ L₁ + 1 / (t - 1) := by
    have := log_le_sub_one_of_pos (div_pos ht0 (by linarith : (0 : ℝ) < t - 1))
    rw [log_div (by linarith) (by linarith)] at this
    have : t - 1 ≠ 0 := by linarith
    have e : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  rw [hel] at hint
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hMt : bigM t ≤ t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    rw [div_le_iff₀ ht0] at hint
    linarith
  have hq0 : 0 < q := by linarith
  have hq' : 0 ≤ 1 - q⁻¹ := by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hq1.le
  -- reduce to a polynomial inequality in `q`
  have hq4 : 0 < q ^ 4 - 1 / 2 := by nlinarith
  have hD : 0 < L₁ * q * (q ^ 4 - 1 / 2) := by positivity
  have key : log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / l)) < 2 * (t / (t - 1) ^ 2) := by
    have hy : (t - 1) ^ 2 = q ^ 4 := by rw [← hq2]; ring
    have e1 : log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / l)) =
        t * (2 * (log t * (q - 1)) / (L₁ * q * (q ^ 4 - 1 / 2))) := by
      rw [hl, hy]
      field_simp
    have e2 : 2 * (t / (t - 1) ^ 2) = t * (2 / q ^ 4) := by
      rw [hy]; ring
    rw [e1, e2]
    refine mul_lt_mul_of_pos_left ?_ ht0
    rw [div_lt_div_iff₀ hD (by positivity)]
    -- `log t (q-1) q⁴ < L₁ q (q⁴ - 1/2)` using `log t ≤ L₁ + 1/q²`
    have hLt' : log t ≤ L₁ + 1 / q ^ 2 := by rwa [hq2]
    have h1 := mul_le_mul_of_nonneg_right hLt'
      (show 0 ≤ (q - 1) * q ^ 4 by have : 0 ≤ q - 1 := by linarith
                                   positivity)
    have h2 : (L₁ + 1 / q ^ 2) * ((q - 1) * q ^ 4) = L₁ * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 := by
      field_simp
    have h3 : L₁ * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 < L₁ * q * (q ^ 4 - 1 / 2) := by
      have hA : 0 < q ^ 4 - q / 2 := by nlinarith
      have hB' : 0 < q ^ 2 * q * (q - 1) + q * (q - 1 / 2) := by
        have : 0 < q - 1 := by linarith
        have : 0 < q - 1 / 2 := by linarith
        positivity
      nlinarith [mul_lt_mul_of_pos_right hL₁1 hA]
    nlinarith
  calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l))) :=
        mul_le_mul_of_nonneg_left hMt hlog0
    _ = log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / l)) * bigM (t - 1) := by ring
    _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB

end IwaniecJacobsthal
