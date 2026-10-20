module

public import IwaniecLinearSieve.LinearSieve.TheoremFourAux

@[expose] public section

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

namespace IwaniecLinearSieve.TheoremFour

/-! ### `L`, `ξ`, `w` in terms of `ℓ = log log 3y` -/

theorem loglog_three_mul_pos {y : ℝ} (hy : 1 < y) : 0 < log (log (3 * y)) :=
  log_pos (one_lt_log_three_mul hy.le)

theorem log_add_log_three {y : ℝ} (hy : 1 < y) :
    log y + log 3 = exp (log (log (3 * y))) := by
  rw [exp_log (by linarith [one_lt_log_three_mul hy.le]), log_mul (by norm_num) (by linarith)]
  ring

theorem xi_mul_rpow {y : ℝ} (hy : 1 < y) :
    xi y * log (log (3 * y)) ^ (11 / 5 : ℝ) = log y := by
  rw [xi, div_mul_cancel₀ _ (rpow_pos_of_pos (loglog_three_mul_pos hy) _).ne']

theorem pntE_rpow_one_div_xi {y : ℝ} (hy : 1 < y) :
    pntE (y ^ (1 / xi y)) = exp (-pntκ * log (log (3 * y)) ^ (11 / 10 : ℝ)) := by
  rw [pntE, log_rpow_one_div_xi hy, sqrt_eq_rpow, ← rpow_mul (loglog_three_mul_pos hy).le]
  norm_num

theorem xi_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ xi y :=
  div_nonneg (log_pos hy).le (rpow_nonneg (loglog_three_mul_pos hy).le _)

theorem xi_le_log {y : ℝ} (hy : 1 < y) (hℓ : 1 ≤ log (log (3 * y))) : xi y ≤ log y :=
  div_le_self (log_pos hy).le (one_le_rpow hℓ (by norm_num))

/-! ### `L⁵ pntE(w) → 0` -/

theorem tendsto_lin_sub_rpow :
    Tendsto (fun ℓ : ℝ => 5 * ℓ - pntκ * ℓ ^ (11 / 10 : ℝ)) atTop atBot := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
    (eventually_ge_atTop (6 / pntκ))
  refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
  filter_upwards [h, eventually_gt_atTop 0] with ℓ h hℓ
  have hsplit : ℓ ^ (11 / 10 : ℝ) = ℓ * ℓ ^ (1 / 10 : ℝ) := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, rpow_add hℓ, rpow_one]
  have h6 : 6 ≤ pntκ * ℓ ^ (1 / 10 : ℝ) := by
    rw [div_le_iff₀ pntκ_pos] at h; linarith
  rw [hsplit]
  nlinarith

theorem tendsto_log_pow_pntE :
    Tendsto (fun y : ℝ => log y ^ 5 * pntE (y ^ (1 / xi y))) atTop (𝓝 0) := by
  have hT : Tendsto (fun y : ℝ => exp (5 * log (log (3 * y)) -
      pntκ * log (log (3 * y)) ^ (11 / 10 : ℝ))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_lin_sub_rpow.comp tendsto_log_log_three_mul)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with y hy
    have := log_pos hy
    have := pntE_pos (y ^ (1 / xi y))
    positivity
  · filter_upwards [eventually_gt_atTop 1] with y hy
    have hL := log_pos hy
    have hLe : log y ≤ exp (log (log (3 * y))) := by
      rw [← log_add_log_three hy]; linarith [log_pos (by norm_num : (1 : ℝ) < 3)]
    rw [pntE_rpow_one_div_xi hy, sub_eq_add_neg, exp_add, ← neg_mul]
    gcongr
    calc log y ^ 5 ≤ exp (log (log (3 * y))) ^ 5 := by gcongr
      _ = _ := by rw [← exp_nat_mul]; norm_num

theorem eventually_one_le_loglog : ∀ᶠ y : ℝ in atTop, 1 ≤ log (log y) :=
  (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop 1)

theorem eventually_mul_pntE_le (K : ℝ) : ∀ᶠ y : ℝ in atTop,
    K * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y)) ≤ 1 := by
  have hK : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  filter_upwards [tendsto_log_pow_pntE.eventually (eventually_le_nhds hK),
    eventually_gt_atTop 1, tendsto_log_log_three_mul.eventually (eventually_ge_atTop 1)]
    with y h1 hy hℓ
  have hL := log_pos hy
  have hξ0 := xi_nonneg hy
  have hξL := xi_le_log hy hℓ
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hsq : xi y ^ 2 * log y ^ 3 ≤ log y ^ 5 := by
    have : xi y ^ 2 ≤ log y ^ 2 := by gcongr
    calc xi y ^ 2 * log y ^ 3 ≤ log y ^ 2 * log y ^ 3 := by gcongr
      _ = log y ^ 5 := by ring
  have h2 : |K| * (log y ^ 5 * pntE (y ^ (1 / xi y))) ≤ |K| * (1 / (|K| + 1)) := by gcongr
  have h3 : |K| * (1 / (|K| + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; linarith
  calc K * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y))
      ≤ |K| * (xi y ^ 2 * log y ^ 3) * pntE (y ^ (1 / xi y)) := by
        rw [mul_assoc K]; gcongr; exact le_abs_self K
    _ ≤ |K| * log y ^ 5 * pntE (y ^ (1 / xi y)) := by gcongr
    _ ≤ 1 := by rw [mul_assoc]; linarith

theorem eventually_delta_mul_le (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ y : ℝ in atTop,
    delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) ≤
      1 + log (log y) ^ 2 / (8 * log y ^ 2) := by
  set A : ℝ := 5 * exp 32 * (exp 32 ^ 2 * 32 ^ 5) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsq := tendsto_pow_atTop (α := ℝ) (two_ne_zero)
  filter_upwards [tendsto_log_pow_pntE.eventually (eventually_le_nhds
      (by positivity : (0 : ℝ) < 1 / (2 * (C + 1)))),
    eventually_gt_atTop 1, tendsto_log_log_three_mul.eventually (eventually_ge_atTop 1),
    tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    (hsq.comp tendsto_log_atTop).eventually (eventually_ge_atTop (A + 1)),
    (hsq.comp (tendsto_log_atTop.comp tendsto_log_atTop)).eventually
      (eventually_ge_atTop (8 * (2 * A + 1)))] with y h1 hy hℓ hL1 hL2 hΛ
  simp only [Function.comp] at hL2 hΛ
  set L := log y
  set b := C * xi y ^ 2 * pntE (y ^ (1 / xi y))
  have hL : 0 < L := by linarith
  have hLsq : 0 < L ^ 2 := by positivity
  have hξ0 := xi_nonneg hy
  have hξL := xi_le_log hy hℓ
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hb0 : 0 ≤ b := by positivity
  -- `b L² ≤ 1/2`
  have hbL : b * L ^ 2 ≤ 1 / 2 := by
    have : xi y ^ 2 * L ^ 2 ≤ L ^ 5 := by
      have : xi y ^ 2 ≤ L ^ 2 := by gcongr
      calc xi y ^ 2 * L ^ 2 ≤ L ^ 2 * L ^ 2 := by gcongr
        _ = L ^ 4 * 1 := by ring
        _ ≤ L ^ 4 * L := by gcongr
        _ = L ^ 5 := by ring
    calc b * L ^ 2 = C * (xi y ^ 2 * L ^ 2) * pntE (y ^ (1 / xi y)) := by ring
      _ ≤ (C + 1) * (L ^ 5 * pntE (y ^ (1 / xi y))) := by
          rw [mul_assoc]; gcongr; linarith
      _ ≤ (C + 1) * (1 / (2 * (C + 1))) := by gcongr
      _ = 1 / 2 := by field_simp
  -- `δ(s₀, y) ≤ exp (A / L²)`
  have hδ : delta (exp 32) y ≤ exp (A / L ^ 2) := by
    rw [delta, log_exp]
    set x := exp 32 ^ 2 * 32 ^ 5 / L ^ 2
    have hx : 0 ≤ x := by positivity
    rw [rpow_def_of_pos (by linarith)]
    apply exp_le_exp.2
    have := log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
    calc log (1 + x) * (5 * exp 32) ≤ x * (5 * exp 32) := by gcongr; linarith
      _ = A / L ^ 2 := by rw [hA]; simp only [x]; ring
  set v := A / L ^ 2 + b
  have hv0 : 0 ≤ v := by positivity
  have hvL : v * L ^ 2 ≤ A + 1 / 2 := by
    have : v * L ^ 2 = A + b * L ^ 2 := by simp only [v]; field_simp
    linarith
  have hv1 : v ≤ 1 := by
    have : v * L ^ 2 ≤ 1 * L ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hLsq
  have hexp : exp v ≤ 1 + 2 * v := by
    have := abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hv0]; exact hv1)
    have := (abs_le.1 this).2
    nlinarith
  have h2v : 2 * v ≤ log (log y) ^ 2 / (8 * L ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc delta (exp 32) y * (1 + b) ≤ exp (A / L ^ 2) * exp b :=
        mul_le_mul hδ (by linarith [add_one_le_exp b]) (by linarith) (exp_pos _).le
    _ = exp v := by rw [← exp_add]
    _ ≤ _ := by linarith

/-! ### The crude bound against the Lemma 9 lower bounds -/

/-- `ξ log ξ - (ξ - 2) log (ξ - 2) ≤ 2 log ξ + 2`. -/
theorem mul_log_sub_le {ξ : ℝ} (hξ : 2 < ξ) :
    ξ * log ξ - (ξ - 2) * log (ξ - 2) ≤ 2 * log ξ + 2 := by
  have hu : 0 < ξ - 2 := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : 0 < ξ) hu)
  rw [log_div (by linarith) hu.ne'] at h
  have h' : (ξ - 2) * (log ξ - log (ξ - 2)) ≤ (ξ - 2) * (ξ / (ξ - 2) - 1) :=
    mul_le_mul_of_nonneg_left h hu.le
  have e : (ξ - 2) * (ξ / (ξ - 2) - 1) = 2 := by field_simp; ring
  nlinarith

/-- The comparisons [I71, (4.4), (4.5), (4.9), (4.10)] in the variable `ℓ = log log 3y`, with
`L = e^ℓ - log 3` and `ξ = L / ℓ^{11/5}`, under explicit "ℓ large" hypotheses. -/
theorem crude_alg {c C' ℓ L ξ : ℝ} (hc : 0 ≤ c) (hC' : 1 ≤ C') (hℓ : 2 ≤ ℓ)
    (hL : L + log 3 = exp ℓ) (hξ : ξ * ℓ ^ (11 / 5 : ℝ) = L) (h2 : 2 * log 3 ≤ exp ℓ)
    (h3 : 4 * ℓ ^ (11 / 5 : ℝ) ≤ exp (ℓ / 2)) (h4 : 11 / 5 * log ℓ + C' ≤ ℓ ^ (1 / 4 : ℝ))
    (h5 : 2 + c + 18 * log 2 ≤ log ℓ / 4) (h6 : 2 + c / 2 + 3 / 4 * log ℓ ≤ ℓ / 8) :
    0 < 11 / 5 * log ℓ + C' ∧ 2 * exp 1 * (11 / 5 * log ℓ + C') ≤ ξ - 2 ∧
    2 * (exp 1 * (11 / 5 * log ℓ + C') / (ξ - 2)) ^ (ξ - 2) * L ^ 4 ≤
      exp (-(ξ / 2 * log (ξ / 2)) - ξ / 2 * log (log (ξ / 2)) - c * (ξ / 2)) ∧
    2 * (exp 1 * (11 / 5 * log ℓ + C') / (ξ - 2)) ^ (ξ - 2) * L ^ 4 ≤
      (1 + (ξ / 2) ^ 2 * log (ξ / 2) ^ 5 / L ^ 2) ^ (5 * (ξ / 2)) *
        exp (-(ξ * log ξ) - ξ * log (log ξ) - c * ξ) := by
  set P := ℓ ^ (11 / 5 : ℝ) with hPdef
  set X := 11 / 5 * log ℓ + C' with hXdef
  have hℓ0 : 0 < ℓ := by linarith
  have hlℓ : 0 < log ℓ := log_pos (by linarith)
  have hPℓ : ℓ ≤ P := self_le_rpow_of_one_le (by linarith) (by norm_num)
  have hP0 : 0 < P := by linarith
  have hl3 : 0 < log 3 := log_pos (by norm_num)
  have hl2 : log 2 < 1 := by have := log_two_lt_d9; linarith
  have hl20 : 0 < log 2 := log_pos (by norm_num)
  have hL0 : 0 < L := by linarith
  have hLe : L ≤ exp ℓ := by linarith
  have hlogL : log L ≤ ℓ := by
    calc log L ≤ log (exp ℓ) := log_le_log hL0 hLe
      _ = ℓ := log_exp ℓ
  have hξdef : ξ = L / P := by rw [← hξ]; field_simp
  have hξ0 : 0 < ξ := by rw [hξdef]; positivity
  have hξL : ξ ≤ L := by rw [hξdef]; exact div_le_self hL0.le (by linarith)
  have hlogξ : log ξ ≤ ℓ := (log_le_log hξ0 hξL).trans hlogL
  -- `ξ ≥ 2 e^{ℓ/2}`
  have hE0 := exp_pos (ℓ / 2)
  have he2 : exp ℓ = exp (ℓ / 2) * exp (ℓ / 2) := by rw [← exp_add]; ring_nf
  have hξbig : 2 * exp (ℓ / 2) ≤ ξ := by
    rw [hξdef, le_div_iff₀ hP0]
    nlinarith [mul_le_mul_of_nonneg_left h3 hE0.le]
  have hlogξ2 : ℓ / 2 ≤ log (ξ / 2) := by
    calc ℓ / 2 = log (exp (ℓ / 2)) := (log_exp _).symm
      _ ≤ log (ξ / 2) := log_le_log hE0 (by linarith)
  -- `X`
  have hX1 : 1 ≤ X := by
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 5) hlℓ.le; linarith
  have hX0 : 0 < X := by linarith
  have hq : ℓ ^ (1 / 4 : ℝ) ≤ ℓ := rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hXℓ : X ≤ ℓ := h4.trans hq
  have hlogX0 : 0 ≤ log X := log_nonneg hX1
  have hlogX : log X ≤ log ℓ / 4 := by
    have := log_le_log hX0 h4
    rw [log_rpow hℓ0] at this; linarith
  have he : exp 1 < 2.72 := by have := exp_one_lt_d9; norm_num at this ⊢; linarith
  have h2e : 2 * exp 1 * X ≤ ξ - 2 := by
    have : exp 1 * X ≤ 2.72 * ℓ := mul_le_mul he.le hXℓ hX0.le (by norm_num)
    linarith
  have hu0 : 0 < ξ - 2 := by linarith
  have hL4 : L ^ 4 = exp (4 * log L) := by
    rw [show (4 : ℝ) * log L = log (L ^ 4) by rw [log_pow]; norm_num, exp_log (by positivity)]
  have hcr : 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * L ^ 4 =
      exp (log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L) := by
    rw [exp_add, exp_add, exp_log two_pos, ← hL4, ← exp_one_mul_div_rpow hX0 hu0]
  -- common bounds
  have hlam0 : 0 < log (ξ / 2) := by linarith
  have hlogu : log (ξ / 2) ≤ log (ξ - 2) := log_le_log (by linarith) (by linarith)
  have hulogu : (ξ - 2) * log (ξ / 2) ≤ (ξ - 2) * log (ξ - 2) :=
    mul_le_mul_of_nonneg_left hlogu hu0.le
  have huX : (ξ - 2) * log X ≤ ξ * log X := mul_le_mul_of_nonneg_right (by linarith) hlogX0
  have hξX : ξ * log X ≤ ξ * (log ℓ / 4) := mul_le_mul_of_nonneg_left hlogX hξ0.le
  have hlamξ : log (ξ / 2) ≤ log ξ := log_le_log (by positivity) (by linarith)
  have hlllam : log (log (ξ / 2)) ≤ log ℓ := log_le_log hlam0 (hlamξ.trans hlogξ)
  refine ⟨hX0, h2e, ?_, ?_⟩ <;> rw [hcr]
  · -- `s ≤ ξ/2`: (4.4), (4.9)
    apply exp_le_exp.2
    have hA1 : (ξ / 2 - 2) * (ℓ / 2) ≤ (ξ / 2 - 2) * log (ξ / 2) :=
      mul_le_mul_of_nonneg_left hlogξ2 (by linarith)
    have hA2 : ξ / 2 * log (log (ξ / 2)) ≤ ξ / 2 * log ℓ :=
      mul_le_mul_of_nonneg_left hlllam (by linarith)
    have hA3 : ξ * (2 + c / 2 + 3 / 4 * log ℓ) ≤ ξ * (ℓ / 8) :=
      mul_le_mul_of_nonneg_left h6 hξ0.le
    have hA4 : ξ / 4 * (ℓ / 2) ≤ (ξ / 2 - 2) * (ℓ / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · -- `s ≥ ξ/2`: (4.5), (4.10)
    set x := (ξ / 2) ^ 2 * log (ξ / 2) ^ 5 / L ^ 2 with hx
    have hx0 : 0 < x := by positivity
    have h1 : exp (log x * (5 * (ξ / 2))) ≤ (1 + x) ^ (5 * (ξ / 2)) := by
      rw [← rpow_def_of_pos hx0]
      exact rpow_le_rpow hx0.le (by linarith) (by positivity)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right h1 (exp_pos _).le)
    rw [← exp_add]
    apply exp_le_exp.2
    have hlogx : log x = 2 * log (ξ / 2) + 5 * log (log (ξ / 2)) - 2 * log L := by
      rw [hx, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow, log_pow, log_pow]
      push_cast; ring
    have hlam : log (ξ / 2) = log L - log 2 - 11 / 5 * log ℓ := by
      rw [hξdef, div_div, log_div hL0.ne' (by positivity), log_mul hP0.ne' (by norm_num),
        hPdef, log_rpow hℓ0]
      ring
    have hlllam' : log ℓ - log 2 ≤ log (log (ξ / 2)) := by
      rw [← log_div hℓ0.ne' (by norm_num)]
      exact log_le_log (by positivity) hlogξ2
    have hlx : 3 / 5 * log ℓ - 7 * log 2 ≤ log x := by rw [hlogx]; linarith
    have hB1 : (3 / 5 * log ℓ - 7 * log 2) * (5 * (ξ / 2)) ≤ log x * (5 * (ξ / 2)) :=
      mul_le_mul_of_nonneg_right hlx (by positivity)
    have hlξ0 : 0 < log ξ := log_pos (by linarith)
    have hB2 : ξ * log (log ξ) ≤ ξ * log ℓ :=
      mul_le_mul_of_nonneg_left (log_le_log hlξ0 hlogξ) hξ0.le
    have hB3 : ξ * (2 + c + 18 * log 2) ≤ ξ * (log ℓ / 4) :=
      mul_le_mul_of_nonneg_left h5 hξ0.le
    have hB4 := mul_log_sub_le (by linarith : 2 < ξ)
    have hB5 : 0 ≤ ξ * log 2 := by positivity
    linarith

/-- The "ℓ large" hypotheses of `crude_alg` hold eventually. -/
theorem eventually_crude_hyp (c C' : ℝ) : ∀ᶠ ℓ : ℝ in atTop,
    2 ≤ ℓ ∧ 2 * log 3 ≤ exp ℓ ∧ 4 * ℓ ^ (11 / 5 : ℝ) ≤ exp (ℓ / 2) ∧
    11 / 5 * log ℓ + C' ≤ ℓ ^ (1 / 4 : ℝ) ∧ 2 + c + 18 * log 2 ≤ log ℓ / 4 ∧
    2 + c / 2 + 3 / 4 * log ℓ ≤ ℓ / 8 := by
  have hF3 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (11 / 5) (1 / 2)
    (by norm_num)).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hF4 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 5)
  have hF6 := isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [eventually_ge_atTop 2, tendsto_exp_atTop.eventually
      (eventually_ge_atTop (2 * log 3)), hF3, hF4, (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)).eventually (eventually_ge_atTop (2 * C')),
    tendsto_log_atTop.eventually (eventually_ge_atTop (4 * (2 + c + 18 * log 2))), hF6,
    eventually_ge_atTop (16 * (2 + |c|))] with ℓ h1 h2 h3 h4 h4' h5 h6 h6'
  have hℓ0 : 0 < ℓ := by linarith
  have hlℓ : 0 ≤ log ℓ := log_nonneg (by linarith)
  refine ⟨h1, h2, ?_, ?_, by linarith, ?_⟩
  · have := mul_le_mul_of_nonneg_right h3 (exp_pos (ℓ / 2)).le
    rw [mul_assoc, ← exp_add, show -(1 / 2) * ℓ + ℓ / 2 = 0 by ring, exp_zero, mul_one] at this
    linarith
  · have hq := rpow_nonneg hℓ0.le (1 / 4 : ℝ)
    rw [norm_of_nonneg hlℓ, norm_of_nonneg hq] at h4
    linarith
  · rw [norm_of_nonneg hlℓ, id, norm_of_nonneg hℓ0.le] at h6
    have := le_abs_self c
    have := abs_nonneg c
    linarith

theorem eventually_crude (c C' : ℝ) (hc : 0 ≤ c) (hC' : 1 ≤ C') : ∀ᶠ y : ℝ in atTop,
    0 < log (log (y ^ (1 / xi y))) + C' ∧
    2 * exp 1 * (log (log (y ^ (1 / xi y))) + C') ≤ xi y - 2 ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      exp (-(xi y / 2 * log (xi y / 2)) - xi y / 2 * log (log (xi y / 2)) - c * (xi y / 2)) ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      delta (xi y / 2) y * exp (-(xi y * log (xi y)) - xi y * log (log (xi y)) - c * xi y) := by
  filter_upwards [tendsto_log_log_three_mul.eventually (eventually_crude_hyp c C'),
    eventually_gt_atTop 1] with y h hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hlw : log (log (y ^ (1 / xi y))) = 11 / 5 * log (log (log (3 * y))) := by
    rw [log_rpow_one_div_xi hy, log_rpow (loglog_three_mul_pos hy)]
  rw [hlw, delta]
  exact crude_alg hc hC' h1 (log_add_log_three hy) (xi_mul_rpow hy) h2 h3 h4 h5 h6

end IwaniecLinearSieve.TheoremFour
