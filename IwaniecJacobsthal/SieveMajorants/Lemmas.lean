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

end IwaniecJacobsthal
