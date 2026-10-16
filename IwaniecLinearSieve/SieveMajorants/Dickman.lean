import IwaniecLinearSieve.SieveMajorants.Asymptotic

/-!
# The Dickman function and its comparison with `𝔐` ([I71, proof of Lemma 9])

The Dickman function `ϱ`: `ϱ = 1` on `(-∞, 1]`, `u ϱ'(u) = -ϱ(u - 1)` for `u > 1`. We build it
with the delay-equation solver of `Delay.lean` (shifted by `2`), and prove:

* `dickman_integral_identity`: `u ϱ(u) = ∫_{u-1}^u ϱ` for `u ≥ 1`;
* `dickman_pos`, `dickman_antitone`, `dickman_le_one`;
* [I71, p. 15] `dickman_le_bigM`: `ϱ(s) = O(𝔐(s))`, since `𝔐` is a supersolution of the
  equation of `ϱ`; and `bigM_add_two_le_dickman`: `𝔐(s + 2) = O(ϱ(s))`, since `𝔐(· + 2)` is a
  subsolution;
* `dickman_asymp`: `ϱ(s) = exp{-s(log s + log log s - 1 + log log s/log s) + O(s/log s)}`,
  transferred from `bigM_asymp`. [I71] quotes this from Hua's book and deduces the asymptotics
  of `𝔐` from it; we go the other way.
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- The delay coefficient of the shifted Dickman equation, made continuous on `ℝ`. -/
noncomputable def dickmanKer (s : ℝ) : ℝ := -(1 / (max s 3 - 2))

theorem continuous_dickmanKer : Continuous dickmanKer := by
  unfold dickmanKer
  refine (continuous_const.div (by fun_prop : Continuous fun x : ℝ => max x 3 - 2)
    fun x => ?_).neg
  have := le_max_right x 3
  linarith

/-- The Dickman function `ϱ`. -/
noncomputable def dickman (u : ℝ) : ℝ := Delay.sol dickmanKer (fun _ => 1) (u + 2)

theorem continuous_dickman : Continuous dickman :=
  (Delay.continuous_sol continuous_dickmanKer continuous_const).comp
    (continuous_id.add continuous_const)

theorem dickman_of_le_one {u : ℝ} (hu : u ≤ 1) : dickman u = 1 :=
  Delay.sol_of_le (by linarith)

theorem hasDerivAt_dickman {u : ℝ} (hu : 1 < u) :
    HasDerivAt dickman (-(dickman (u - 1) / u)) u := by
  have h := (Delay.hasDerivAt_sol (y₀ := fun _ => (1 : ℝ)) continuous_dickmanKer continuous_const
    (show 3 < u + 2 by linarith)).comp u ((hasDerivAt_id u).add_const 2)
  refine h.congr_deriv ?_
  simp only [dickmanKer, mul_one, dickman]
  rw [max_eq_left (by linarith), show u + 2 - 1 = u - 1 + 2 by ring]
  ring

/-- `u ϱ(u) = ∫_{u-1}^u ϱ` for `u ≥ 1`. -/
theorem dickman_integral_identity {u : ℝ} (hu : 1 ≤ u) :
    u * dickman u = ∫ x in (u - 1)..u, dickman x := by
  set g : ℝ → ℝ := fun t => t * dickman t - ∫ x in (t - 1)..t, dickman x
  have hgc : ContinuousOn g (Ici 1) := by
    refine ContinuousOn.sub (continuous_id.mul continuous_dickman).continuousOn ?_
    exact fun t _ => (hasDerivAt_integral_unit continuous_dickman t).continuousAt
      |>.continuousWithinAt
  have hgd : ∀ t, 1 < t → HasDerivAt g 0 t := by
    intro t ht
    have := ((hasDerivAt_id t).mul (hasDerivAt_dickman ht)).sub
      (hasDerivAt_integral_unit continuous_dickman t)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h1 : g 1 = 0 := by
    simp only [g, sub_self, one_mul, dickman_of_le_one le_rfl]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx; exact dickman_of_le_one hx.2]
    simp
  have := (eq_of_hasDerivAt_zero hgc hgd hu).trans h1
  simp only [g] at this
  linarith

theorem dickman_pos (u : ℝ) : 0 < dickman u := by
  rcases le_total u 1 with hu | hu
  · rw [dickman_of_le_one hu]; norm_num
  refine pos_of_first_crossing (f := dickman) (a₀ := 1) (a := 1) continuous_dickman.continuousOn
    (fun x hx => by rw [dickman_of_le_one hx.2]; norm_num)
    (by rw [dickman_of_le_one le_rfl]; norm_num) ?_ u hu
  intro t ht _ hpos
  have hpos' : ∀ x, x < t → 0 < dickman x := fun x hx => by
    rcases le_total x 1 with h | h
    · rw [dickman_of_le_one h]; norm_num
    · exact hpos x ⟨h, hx⟩
  have hI : 0 < ∫ x in (t - 1)..t, dickman x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_dickman.intervalIntegrable _ _)
      (fun x hx => hpos' x hx.2) (by linarith)
  rw [← dickman_integral_identity ht.le] at hI
  exact pos_of_mul_pos_right hI (by linarith)

theorem dickman_antitone : Antitone dickman := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 1) (fun x hx y hy _ => ?_) ?_
  · rw [dickman_of_le_one hx, dickman_of_le_one hy]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
    (f' := fun u => -(dickman (u - 1) / u)) continuous_dickman.continuousOn
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx
    exact (hasDerivAt_dickman hx).hasDerivWithinAt
  · rw [interior_Ici] at hx
    have : 0 < dickman (x - 1) / x := div_pos (dickman_pos _) (by linarith [hx.out])
    linarith

theorem dickman_le_one (u : ℝ) : dickman u ≤ 1 := by
  rcases le_total u 1 with hu | hu
  · rw [dickman_of_le_one hu]
  · rw [← dickman_of_le_one le_rfl]; exact dickman_antitone hu

/-! ### Comparison with `𝔐` -/

/-- From (3.12): `∫_{s-1}^s 𝔐 ≤ (s-1)²/s 𝔐(s)` for `s ≥ 3`. -/
theorem integral_bigM_le_sq_div_mul {s : ℝ} (hs : 3 ≤ s) :
    ∫ x in (s - 1)..s, bigM x ≤ (s - 1) ^ 2 / s * bigM s := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < (s - 1) ^ 2 := by nlinarith
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2) with hw₀
  have hw0 : 0 < w₀ := (weight_mem (x := s - 1) (by linarith)).1
  have hI : w₀ * ∫ x in (s - 1)..s, bigM x ≤ ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.mul continuous_bigM).intervalIntegrable _ _)
      (ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        (continuousOn_weight_mul continuous_bigM (by linarith))) fun x hx => ?_
    have hwx : w₀ ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
        one_div_le_one_div_of_le (by nlinarith) (by nlinarith [hx.1])
      rw [hw₀]; linarith
    exact mul_le_mul_of_nonneg_right hwx (bigM_pos x).le
  rw [← coefA_mul_bigM hs] at hI
  have e : coefA s = w₀ * ((s - 1) ^ 2 / s) := by
    have : s - 1 ≠ 0 := by linarith
    rw [coefA, hw₀]; field_simp
  rw [e, mul_assoc] at hI
  exact le_of_mul_le_mul_left hI hw0

/-- [I71, p. 15]: `ϱ(s) = O(𝔐(s))`. -/
theorem dickman_le_bigM : ∃ C, ∀ s, dickman s ≤ C * bigM s := by
  have hM4 := bigM_pos 4
  set C := 2 / bigM 4 with hC
  have hC0 : 0 < C := by positivity
  have hCM : ∀ x ≤ 4, 2 ≤ C * bigM x := fun x hx => by
    have : C * bigM 4 = 2 := by rw [hC]; field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left (bigM_antitone hx) hC0.le
  refine ⟨C, fun s => ?_⟩
  rcases le_total s 3 with hs | hs
  · linarith [dickman_le_one s, hCM s (by linarith)]
  refine (lt_of_sub_super (A := id) (w := fun _ => 1) (f := dickman)
    (g := fun x => C * bigM x) (a := 4) continuous_dickman.continuousOn
    (continuous_const.mul continuous_bigM).continuousOn continuousOn_const
    (fun _ _ => one_pos) (fun s hs => by simp only [id]; linarith) (fun s hs => ?_)
    (fun s hs => ?_) (fun x hx => ?_) s (by linarith)).le
  · simp only [id, one_mul]
    rw [dickman_integral_identity (by linarith)]
  · simp only [id, one_mul]
    rw [intervalIntegral.integral_const_mul]
    have h1 := integral_bigM_le_sq_div_mul (s := s) (by linarith)
    have h2 : (s - 1) ^ 2 / s * bigM s ≤ s * bigM s := by
      refine mul_le_mul_of_nonneg_right ?_ (bigM_pos s).le
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  · show dickman x < C * bigM x
    linarith [dickman_le_one x, hCM x hx.2]

/-- [I71, p. 15]: `𝔐(s + 2) = O(ϱ(s))`. -/
theorem bigM_add_two_le_dickman : ∃ C, ∀ s, bigM (s + 2) ≤ C * dickman s := by
  have hr2 := dickman_pos 2
  set C := 4 / dickman 2 with hC
  have hC0 : 0 < C := by positivity
  have hCr : ∀ x ≤ 2, 4 ≤ C * dickman x := fun x hx => by
    have : C * dickman 2 = 4 := by rw [hC]; field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left (dickman_antitone hx) hC0.le
  refine ⟨C, fun s => ?_⟩
  rcases le_total s 1 with hs | hs
  · linarith [bigM_le_three (s + 2), hCr s (by linarith)]
  refine (lt_of_sub_super (A := id) (w := fun _ => 1) (f := fun x => bigM (x + 2))
    (g := fun x => C * dickman x) (a := 2)
    (continuous_bigM.comp (continuous_id.add continuous_const)).continuousOn
    (continuous_const.mul continuous_dickman).continuousOn continuousOn_const
    (fun _ _ => one_pos) (fun s hs => by simp only [id]; linarith) (fun s hs => ?_)
    (fun s hs => ?_) (fun x hx => ?_) s (by linarith)).le
  · simp only [id, one_mul]
    have h := bigM_lt_integral (s := s + 2) (by linarith)
    rw [show s + 2 - 2 = s by ring, show s + 2 - 1 = s + 1 by ring] at h
    have e : ∫ x in (s - 1)..s, bigM (x + 2) = ∫ x in (s + 1)..(s + 2), bigM x := by
      rw [intervalIntegral.integral_comp_add_right (fun x => bigM x) 2]
      ring_nf
    rw [e]
    have hs0 : 0 < s := by linarith
    rw [one_div_mul_eq_div, lt_div_iff₀ hs0] at h
    linarith
  · simp only [id, one_mul]
    rw [intervalIntegral.integral_const_mul, ← dickman_integral_identity (by linarith)]
    exact le_of_eq (by ring)
  · show bigM (x + 2) < C * dickman x
    linarith [bigM_le_three (x + 2), hCr x hx.2]

/-- `Φ₀(s + 2) - Φ₀(s) ≤ 16 s / log s` for `s ≥ 9`. -/
theorem asymPhi_add_two_sub_le {s : ℝ} (hs : 9 ≤ s) :
    asymPhi 0 (s + 2) - asymPhi 0 s ≤ 16 * (s / log s) := by
  -- `ψ₀(L) ≤ 4 L` for `L ≥ 2`
  have hpsi : ∀ L, 2 ≤ L → asymPsi 0 L ≤ 4 * L := by
    intro L hL
    obtain ⟨hl0, hl1⟩ := log_le_sub_one_of_two_le hL
    unfold asymPsi
    have h1 : (log L + 0 + 1) / L ≤ L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h3 : -((log L + 0 - 1) / L ^ 2) ≤ 1 / L ^ 2 := by
      rw [← neg_div, div_le_div_iff_of_pos_right (by positivity)]; linarith
    have h4 : 1 / L ^ 2 ≤ L := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hL2 : 2 ≤ log s := two_le_log_of_eight_le (by linarith)
  have e1 := (asymPhi_sub_mem (c := 0) (by norm_num) (s := s + 2) (x := s + 1) (by linarith)
    (by linarith) (by linarith)).2
  have e2 := (asymPhi_sub_mem (c := 0) (by norm_num) (s := s + 1) (x := s) (by linarith)
    (by linarith) (by linarith)).2
  have hl1 : log (s + 1) ≤ log (s + 2) := log_le_log (by linarith) (by linarith)
  have hl2 : log (s + 2) ≤ 2 * log s := by
    rw [← log_rpow (by linarith)]
    exact log_le_log (by linarith) (by norm_num; nlinarith)
  have hp1 := hpsi _ (hL2.trans (log_le_log (by linarith) (by linarith : s ≤ s + 2)))
  have hp2 := hpsi _ (hL2.trans (log_le_log (by linarith) (by linarith : s ≤ s + 1)))
  have hsq : log s ≤ s / log s := by
    rw [le_div_iff₀ (by linarith), ← sq]; exact log_sq_le (by linarith)
  nlinarith

/-- **The asymptotics of the Dickman function** (de Bruijn; [I71, p. 15], quoted from Hua):
`ϱ(s) = exp{-s(log s + log log s - 1 + log log s/log s) + O(s/log s)}`. -/
theorem dickman_asymp : ∃ C s₀ : ℝ, ∀ s ≥ s₀,
    |Real.log (dickman s) + s * (Real.log s + Real.log (Real.log s) - 1 +
      Real.log (Real.log s) / Real.log s)| ≤ C * s / Real.log s := by
  obtain ⟨C, s₀, hM⟩ := bigM_asymp
  obtain ⟨C₁, h₁⟩ := dickman_le_bigM
  obtain ⟨C₂, h₂⟩ := bigM_add_two_le_dickman
  have hC₁ : 0 < C₁ := by
    have := h₁ 0
    by_contra h; push Not at h
    nlinarith [dickman_pos 0, bigM_pos 0]
  have hC₂ : 0 < C₂ := by
    have := h₂ 0
    have hb := bigM_pos (0 + 2)
    by_contra h; push Not at h
    nlinarith [dickman_pos 0]
  refine ⟨|log C₁| + |log C₂| + 2 * |C| + 16, max s₀ 9, fun s hs => ?_⟩
  have hs9 : 9 ≤ s := le_of_max_le_right hs
  have hs0 : 0 < s := by linarith
  have hL : 0 < log s := log_pos (by linarith)
  have hsL : 1 ≤ s / log s := by
    rw [le_div_iff₀ hL, one_mul]; linarith [log_le_sub_one_of_pos hs0]
  have hr := dickman_pos s
  have e0 : ∀ t, t * (log t + log (log t) - 1 + log (log t) / log t) = asymPhi 0 t := by
    intro t; unfold asymPhi; rw [add_zero]
  rw [e0]
  -- upper bound from `ϱ ≤ C₁ 𝔐`
  have hu := (abs_le.1 (hM s (le_of_max_le_left hs))).2
  rw [e0] at hu
  have l1 : log (dickman s) ≤ log C₁ + log (bigM s) := by
    rw [← log_mul hC₁.ne' (bigM_pos s).ne']; exact log_le_log hr (h₁ s)
  -- lower bound from `𝔐(s+2) ≤ C₂ ϱ(s)`
  have hl := (abs_le.1 (hM (s + 2) (by linarith [le_of_max_le_left hs]))).1
  rw [e0] at hl
  have l2 : log (bigM (s + 2)) ≤ log C₂ + log (dickman s) := by
    rw [← log_mul hC₂.ne' hr.ne']; exact log_le_log (bigM_pos _) (h₂ s)
  have hΦ := asymPhi_add_two_sub_le hs9
  have hs2 : (s + 2) / log (s + 2) ≤ 2 * (s / log s) := by
    have : log s ≤ log (s + 2) := log_le_log hs0 (by linarith)
    rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc]
    calc s + 2 ≤ 2 * s := by linarith
      _ = (2 * s / log s) * log s := by field_simp
      _ ≤ (2 * s / log s) * log (s + 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = log (s + 2) * 2 * (s / log s) := by ring
  have e1 : C * (s + 2) / log (s + 2) = C * ((s + 2) / log (s + 2)) := by ring
  have e2 : C * s / log s = C * (s / log s) := by ring
  have e3 : (|log C₁| + |log C₂| + 2 * |C| + 16) * s / log s =
      |log C₁| * (s / log s) + |log C₂| * (s / log s) + 2 * (|C| * (s / log s)) +
        16 * (s / log s) := by ring
  rw [e1] at hl
  rw [e2] at hu
  rw [e3, abs_le]
  have k1 : C * ((s + 2) / log (s + 2)) ≤ 2 * (|C| * (s / log s)) := by
    rw [mul_left_comm]
    have hpos : 0 ≤ (s + 2) / log (s + 2) :=
      div_nonneg (by linarith) (log_nonneg (by linarith))
    calc C * ((s + 2) / log (s + 2)) ≤ |C| * ((s + 2) / log (s + 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hpos
      _ ≤ |C| * (2 * (s / log s)) := mul_le_mul_of_nonneg_left hs2 (abs_nonneg C)
  have k2 : C * (s / log s) ≤ |C| * (s / log s) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have k3 := le_abs_self (log C₁)
  have k4 := le_abs_self (log C₂)
  have k5 : 0 ≤ |log C₁| := abs_nonneg _
  have k6 : 0 ≤ |log C₂| := abs_nonneg _
  have k7 : 0 ≤ |C| := abs_nonneg _
  have k8 : |log C₁| ≤ |log C₁| * (s / log s) := le_mul_of_one_le_right k5 hsL
  have k9 : |log C₂| ≤ |log C₂| * (s / log s) := le_mul_of_one_le_right k6 hsL
  have k10 : 0 ≤ |C| * (s / log s) := mul_nonneg k7 (by linarith)
  constructor <;> linarith

end IwaniecLinearSieve
