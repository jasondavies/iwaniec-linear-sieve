module

public import IwaniecLinearSieve.Jacobsthal.ShiftedSieve
public import IwaniecLinearSieve.Main.TheoremOne
public import IwaniecLinearSieve.EulerGamma.LemmaFive

@[expose] public section

/-!
# [I78, Lemma 2]

[I78, §3] takes Rosser's lower-bound weights for the primes `p < z`,

    λ_n = μ(n)   if n = p₁ ⋯ p_u, p₁ > ⋯ > p_u, p₁ ⋯ p_{2l} < y p_{2l}^{-2} for 2l ≤ u,
    λ_n = 0      otherwise

(`rosserWeight y z`, supported on `D⁻ = rosserSet true y z`; condition (−) of [I78, Lemma 1] is
`sum_powerset_rosserWeight_le`), and quotes from [I71], for `4 ≤ z² ≤ y < z⁴` and
`s = log y / log z`:

    (5)   ∑_{n ∣ P} |λ_n| ≪ y (log y)^{-2},
    (6)   ∑_{n ∣ P} σ_n / ∏_{p ∣ n} (p - 1) = 2 e^γ log (s - 1) / s + O(1 / log y).

* `lemma2_sum_abs_le` is (5), from [I71, Theorem 5].
* `lemma2_sum_sigma_ge` is the lower half of (6), from [I71, Theorem 4] (in the form
  `Main.exists_fail_div_R_le`) and [I71, Lemma 5] (`f(s) = s - 2e^γ log (s - 1)` on `[2, 4]`,
  `fSieve_eq_of_mem_Icc`). The left side of (6) is `∑_{d ∈ D⁻} μ(d)/d / R(z)`
  (`sum_sigma_div_eq`).

**[I71] proves only the lower half of (6)**: [I71, Theorem 4] is an upper bound for the deficit
`R(z) - ∑_{d ∈ D⁻} μ(d)/d` (its `Q_{r,y}(s)`), and nothing in [I71] bounds the deficit from below,
so the `O(1/log y)` in (6) is two-sided only by appeal to the optimality of the linear sieve, which
[I78] calls "seem[ing] to be best possible". The proof of [I78, Theorem] uses only the lower
half (`lemma2_sum_sigma_ge`). The trivial upper half `∑_{n ∣ P} σ_n / ∏ (p - 1) ≤ 1` is
`sum_sigma_div_le_one`.
-/

open Finset Real

namespace IwaniecLinearSieve

/-- `δ(s, y) ≤ (1 + 16 log⁵ 4)^{20}` for `1 ≤ s ≤ 4` and `log y ≥ 1`. -/
theorem delta_le_of_le_four {s y : ℝ} (hs1 : 1 ≤ s) (hs4 : s ≤ 4) (hy : 1 ≤ log y) :
    delta s y ≤ (1 + 16 * log 4 ^ 5) ^ (20 : ℝ) := by
  have hl0 : 0 ≤ log s := log_nonneg hs1
  have hl4 : log s ≤ log 4 := log_le_log (by linarith) hs4
  have hx : s ^ 2 * log s ^ 5 / log y ^ 2 ≤ 16 * log 4 ^ 5 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 ≤ 16 := by nlinarith
    have h2 : log s ^ 5 ≤ log 4 ^ 5 := by gcongr
    have h3 : 1 ≤ log y ^ 2 := by nlinarith
    have h4 : s ^ 2 * log s ^ 5 ≤ 16 * log 4 ^ 5 :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h5 : 0 ≤ log 4 ^ 5 := by positivity
    nlinarith
  have hx0 : 0 ≤ s ^ 2 * log s ^ 5 / log y ^ 2 := by positivity
  rw [delta]
  calc (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s)
      ≤ (1 + 16 * log 4 ^ 5) ^ (5 * s) := rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ (1 + 16 * log 4 ^ 5) ^ (20 : ℝ) :=
        rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- `z = y^{1/s}` for `s = log y / log z`. -/
theorem rpow_one_div_log_div_log {y z : ℝ} (hz : 1 < z) (hy : 1 < y) :
    y ^ (1 / (log y / log z)) = z := by
  have hlz : log z ≠ 0 := (log_pos hz).ne'
  have hly : log y ≠ 0 := (log_pos hy).ne'
  rw [rpow_def_of_pos (by linarith), show log y * (1 / (log y / log z)) = log z by field_simp,
    exp_log (by linarith)]

/-- The range `z ≥ 2`, `z² ≤ y < z⁴` of [I78, Lemma 2]: `1 < z`, `4 ≤ y`, and
`s = log y / log z ∈ [2, 4)`. -/
theorem lemma2_range {y z : ℝ} (hz : 2 ≤ z) (hzy : z ^ 2 ≤ y) (hyz : y < z ^ 4) :
    1 < z ∧ 4 ≤ y ∧ 2 ≤ log y / log z ∧ log y / log z < 4 := by
  have hz1 : 1 < z := by linarith
  have hlz : 0 < log z := log_pos hz1
  have hz2 : 0 < z ^ 2 := by positivity
  refine ⟨hz1, by nlinarith, ?_, ?_⟩
  · rw [le_div_iff₀ hlz]
    have := log_le_log hz2 hzy
    rw [log_pow] at this
    push_cast at this
    linarith
  · rw [div_lt_iff₀ hlz]
    have := log_lt_log (hz2.trans_le hzy) hyz
    rw [log_pow] at this
    push_cast at this
    linarith

/-- **[I78, Lemma 2], (5)** ([I71, Theorem 5]): for `z ≥ 2` and `z² ≤ y < z⁴`,
`∑_{n ∣ P} |λ_n| ≪ y / log² y`. -/
theorem lemma2_sum_abs_le : ∃ K : ℝ, ∀ y z : ℝ, 2 ≤ z → z ^ 2 ≤ y → y < z ^ 4 →
    ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| ≤ K * y / log y ^ 2 := by
  obtain ⟨c₇, hc₇, h5⟩ := theorem5
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  set y₀ := max y₅ 3
  set D := (1 + 16 * log 4 ^ 5) ^ (20 : ℝ) with hD
  refine ⟨max (c₇ * D * 2) (log y₀ ^ 2), fun y z hz hzy hyz => ?_⟩
  obtain ⟨hz1, hy4, hs2, hs4⟩ := lemma2_range hz hzy hyz
  have hy1 : 1 < y := by linarith
  have hly : 0 < log y := log_pos hy1
  set s := log y / log z
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div_log hz1 hy1
  refine (sum_abs_rosserWeight_le y z).trans ?_
  have hyL : 0 ≤ y / log y ^ 2 := by positivity
  rcases le_or_gt y₀ y with hy0 | hy0
  · obtain ⟨-, hξ, -, -⟩ := hxi y (le_of_max_le_left hy0)
    have hL1 : 1 ≤ log y := by
      have := log_le_log (by norm_num) (le_of_max_le_right hy0)
      linarith [one_lt_log_three]
    have hsξ : s ≤ xi y := by linarith [add_one_le_exp (32 : ℝ)]
    have h := h5 #(primesLT z) true y s hy1 hs2 hsξ
    rw [hzs, filter_true_of_mem fun d hd => card_le_card (primeFactors_subset_of_mem_rosserSet hd)]
      at h
    refine h.trans ?_
    have hδ := delta_le_of_le_four (by linarith) hs4.le hL1 (s := s)
    have hδ0 := delta_pos (by linarith : (1 : ℝ) ≤ s) y
    have hG := errMaj_le_two true s
    have hG0 := errMaj_pos true s
    have hφ : ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hφ0 : (0 : ℝ) ≤ ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) := by
      positivity
    calc c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s * y /
          log y ^ 2
        = c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s *
            (y / log y ^ 2) := by ring
      _ ≤ c₇ * 1 * D * 2 * (y / log y ^ 2) := by gcongr
      _ ≤ max (c₇ * D * 2) (log y₀ ^ 2) * (y / log y ^ 2) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hyL
      _ = _ := by ring
  · -- small `y`: `#D⁻ ≤ y ≤ log² y₀ · y / log² y`
    have h := TheoremFive.card_rosserSet_le (lower := true) hy1 (by linarith : (1 : ℝ) ≤ s)
    rw [hzs] at h
    refine h.trans ?_
    have hl : log y ≤ log y₀ := log_le_log (by linarith) hy0.le
    have hl2 : log y ^ 2 ≤ log y₀ ^ 2 := pow_le_pow_left₀ hly.le hl 2
    calc y = log y ^ 2 * (y / log y ^ 2) := by field_simp
      _ ≤ log y₀ ^ 2 * (y / log y ^ 2) := mul_le_mul_of_nonneg_right hl2 hyL
      _ ≤ max (c₇ * D * 2) (log y₀ ^ 2) * (y / log y ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hyL
      _ = _ := by ring

/-- The left side of [I78, (6)]: `∑_{n ∣ P} σ_n / ∏_{p ∣ n} (p - 1) = (∑_{d ∈ D⁻} μ(d)/d) / R(z)`
(by `sum_powerset_div_prod`, i.e. [I78, Lemma 1] with `f = g`). -/
theorem sum_sigma_div_eq (y z : ℝ) :
    ∑ B ∈ (primesLT z).powerset, (∑ A ∈ B.powerset, rosserWeight y z A) / ∏ p ∈ B, ((p : ℝ) - 1) =
      rosserMain true y z / R z := by
  have h := sum_powerset_div_prod (primesLT z) (fun p ↦ (p : ℝ))
    (fun p hp ↦ ⟨by exact_mod_cast (prime_of_mem_primesLT hp).ne_zero,
      by exact_mod_cast (prime_of_mem_primesLT hp).one_lt.ne'⟩) (rosserWeight y z)
  rw [← rosserMain_eq_sum_rosserWeight] at h
  rw [h]
  exact (mul_div_cancel_left₀ _ (R_pos z).ne').symm

/-- The trivial upper half of [I78, (6)]: `∑_{n ∣ P} σ_n / ∏_{p ∣ n} (p - 1) ≤ 1`. -/
theorem sum_sigma_div_le_one (y z : ℝ) :
    ∑ B ∈ (primesLT z).powerset, (∑ A ∈ B.powerset, rosserWeight y z A) / ∏ p ∈ B, ((p : ℝ) - 1) ≤
      1 := by
  rw [sum_sigma_div_eq, div_le_one (R_pos z)]
  exact rosserMain_true_le_R y z

/-- `-#D⁻ ≤ ∑_{d ∈ D⁻} μ(d)/d`. -/
theorem neg_card_le_rosserMain (y z : ℝ) : -(#(rosserSet true y z) : ℝ) ≤ rosserMain true y z := by
  rw [rosserMain, card_eq_sum_ones, Nat.cast_sum, ← sum_neg_distrib]
  refine sum_le_sum fun d hd ↦ ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast pos_of_mem_rosserSet hd
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have : |(ArithmeticFunction.moebius d : ℝ) / d| ≤ 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < d), div_le_one (by linarith)]
    linarith
  push_cast
  linarith [neg_abs_le ((ArithmeticFunction.moebius d : ℝ) / d)]

/-- `2 e^γ log (s - 1) / s ≤ 3` for `2 ≤ s ≤ 4`. -/
theorem two_exp_mul_log_div_le_three {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    2 * exp eulerMascheroniConstant * log (s - 1) / s ≤ 3 := by
  have hγ : exp eulerMascheroniConstant ≤ exp 1 :=
    exp_le_exp.2 (by linarith [eulerMascheroniConstant_lt_two_thirds])
  have he := exp_one_lt_d9
  have hl : log (s - 1) ≤ s - 2 := by linarith [log_le_sub_one_of_pos (by linarith : 0 < s - 1)]
  have hl0 : 0 ≤ log (s - 1) := log_nonneg (by linarith)
  have hγ0 := exp_pos eulerMascheroniConstant
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **[I78, Lemma 2], (6)**, lower half ([I71, Theorem 4] and [I71, Lemma 5]): for `z ≥ 2`,
`z² ≤ y < z⁴` and `s = log y / log z`,
`∑_{n ∣ P} σ_n / ∏_{p ∣ n} (p - 1) ≥ 2 e^γ log (s - 1) / s - C / log y`. -/
theorem lemma2_sum_sigma_ge : ∃ C : ℝ, 0 ≤ C ∧ ∀ y z : ℝ, 2 ≤ z → z ^ 2 ≤ y → y < z ^ 4 →
    2 * exp eulerMascheroniConstant * log (log y / log z - 1) / (log y / log z) - C / log y ≤
      ∑ B ∈ (primesLT z).powerset, (∑ A ∈ B.powerset, rosserWeight y z A) /
        ∏ p ∈ B, ((p : ℝ) - 1) := by
  obtain ⟨C₁, y₀, hC₁, hy₀, h4⟩ := Main.exists_fail_div_R_le
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  set Y := max (max y₀ y₅) 4
  have hY4 : 4 ≤ Y := le_max_right _ _
  have hlY : 0 < log Y := log_pos (by linarith)
  set D := (1 + 16 * log 4 ^ 5) ^ (20 : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  set C := max (C₁ * D * 3) ((3 + Y / R Y) * log Y)
  have hC0 : 0 ≤ C := le_max_of_le_left (by positivity)
  refine ⟨C, hC0, fun y z hz hzy hyz => ?_⟩
  obtain ⟨hz1, hy4, hs2, hs4⟩ := lemma2_range hz hzy hyz
  have hy1 : 1 < y := by linarith
  have hly : 0 < log y := log_pos hy1
  set s := log y / log z
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div_log hz1 hy1
  rw [sum_sigma_div_eq]
  rcases le_or_gt Y y with hyY | hyY
  · have hy0 : y₀ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hyY)
    obtain ⟨-, hξ, -, -⟩ := hxi y ((le_max_right _ _).trans ((le_max_left _ _).trans hyY))
    have hsξ : s ≤ xi y := by linarith [add_one_le_exp (32 : ℝ)]
    obtain ⟨-, hf⟩ := h4 (#(primesLT z) + 1) true y s hy0 hs2 hsξ
    rw [hzs] at hf
    rw [rosserMain_true_eq (Nat.lt_succ_self _) y, sub_div, div_self (R_pos z).ne']
    have hL1 : 1 ≤ log y := by
      have := log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ y)
      linarith [one_lt_log_three]
    have hδ := delta_le_of_le_four (by linarith) hs4.le hL1 (s := s)
    have hδ0 := delta_pos (by linarith : (1 : ℝ) ≤ s) y
    have hM := bigM_le_three s
    have hM0 := (bigM_pos s).le
    have hmain : 2 * exp eulerMascheroniConstant * log (s - 1) / s = 1 - mainMaj true s / s := by
      simp only [mainMaj]
      rw [fSieve_eq_of_mem_Icc ⟨hs2, hs4.le⟩]
      field_simp
      ring
    have herr : C₁ * delta s y * bigM s / log y ≤ C / log y := by
      refine div_le_div_of_nonneg_right ?_ hly.le
      calc C₁ * delta s y * bigM s ≤ C₁ * D * 3 := by gcongr
        _ ≤ C := le_max_left _ _
    rw [hmain]
    linarith
  · -- small `y`: the left side is `≤ 3 - C / log Y ≤ -Y / R(Y)`, the right side `≥ -y / R(z)`
    have hzY : z ≤ Y := by nlinarith
    have hRz : R Y ≤ R z := R_antitone hzY
    have hRY := R_pos Y
    have hcard := TheoremFive.card_rosserSet_le (lower := true) hy1 (by linarith : (1 : ℝ) ≤ s)
    rw [hzs] at hcard
    have hrm : -(Y / R Y) ≤ rosserMain true y z / R z := by
      rw [le_div_iff₀ (R_pos z)]
      have h1 := neg_card_le_rosserMain y z
      have h2 : Y / R Y * R z ≥ y := by
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hRY]
        nlinarith [R_pos z]
      linarith
    have hmain := two_exp_mul_log_div_le_three hs2 hs4.le
    have hCL : 3 + Y / R Y ≤ C / log y := by
      rw [le_div_iff₀ hly]
      have hl : log y ≤ log Y := log_le_log (by linarith) hyY.le
      have h0 : 0 ≤ 3 + Y / R Y := by positivity
      calc (3 + Y / R Y) * log y ≤ (3 + Y / R Y) * log Y := mul_le_mul_of_nonneg_left hl h0
        _ ≤ C := le_max_right _ _
    linarith

end IwaniecLinearSieve
