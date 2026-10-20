module

public import IwaniecLinearSieve.General.RosserK
public import IwaniecLinearSieve.LinearSieve.TheoremFourAux

@[expose] public section

/-!
# [I71, Lemmas 14 and 16]

[I71, Lemma 14] (`∑_{b < p < a} 1/(p log p) = 1/log b - 1/log a + O(exp(-√log b))`) is
`lemma14` in `IwaniecLinearSieve.PrimeSums.Lemma13`, with `exp(-√log b)` replaced by `pntE b`.

[I71, Lemma 16]: with

    d_{2,y}(s) = ∑_{y₁^{1/3} ≤ p₂ < p₁ < y^{1/s}} R(p₂) / (p₁ p₂),   y₁ = y / p₁

(`d2 y s`, which is our depth-two lower-sieve deficit `fail true 2 y (y^{1/s})`, `d2_eq_fail`),
`e^γ d_{2,y}(s) < g₂(s) / log y + c₆ exp(-√(log y / 6))` for `y > 1`, `s ≥ 2`. As in
`theorem4`, `e^{-γ}` is replaced by the constant `cR` of `R(z) log z → cR` (taken as a
hypothesis), and `exp(-√(log y / 6))` by `pntE (y^{1/6})`.

The proof follows [I71]: only `p₁ ≥ y^{1/4}` contribute, the inner sum is
`R(y₁^{1/3}) - R(p₁)` exactly (`d2_eq_sum`, by telescoping instead of Lemma 14), and the outer
sum is evaluated by Lemma 13 (`lemma13_param`), using
`∫_s^4 (3/(t-1) - 1) dt = g₂(s)` (`integral_lemma16`).
-/

open Real Finset

namespace IwaniecLinearSieve

/-- Iwaniec's `d_{2,y}(s) = ∑_{y₁^{1/3} ≤ p₂ < p₁ < y^{1/s}} R(p₂) / (p₁ p₂)`, `y₁ = y / p₁`. -/
noncomputable def d2 (y s : ℝ) : ℝ :=
  ∑ p₁ ∈ primesLT (y ^ (1 / s)), ∑ p₂ ∈ (primesLT p₁).filter
    (fun p₂ : ℕ ↦ (y / p₁) ^ ((1 : ℝ) / 3) ≤ p₂), R p₂ / (p₁ * p₂)

/-- `d_{2,y}(s)` is the depth-two deficit of the lower sieve: `d_{2,y}(s) = fail true 2 y z`,
`z = y^{1/s}`. -/
theorem d2_eq_fail {y : ℝ} (hy : 0 ≤ y) (s : ℝ) : d2 y s = fail true 2 y (y ^ (1 / s)) := by
  rw [d2, show (2 : ℕ) = 1 + 1 from rfl, fail_true_succ]
  refine sum_congr rfl fun p₁ _ ↦ ?_
  rw [show (1 : ℕ) = 0 + 1 from rfl, fail_false_succ]
  simp only [fail_zero, zero_div, sum_const_zero, zero_add]
  rw [sum_div]
  refine sum_congr (filter_congr fun p₂ _ ↦ ?_) fun p₂ _ ↦ ?_
  · rw [← not_lt, natCast_lt_rpow_one_div_three_iff (div_nonneg hy p₁.cast_nonneg)]
  · rw [div_div, mul_comm (p₁ : ℝ)]

theorem d2_nonneg (y s : ℝ) : 0 ≤ d2 y s :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ div_nonneg (R_nonneg _) (by positivity)

theorem pntE_le_of_log_le {a b : ℝ} (hab : log a ≤ log b) :
    pntE b ≤ pntE a := by
  unfold pntE
  refine exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hab) pntκ_pos.le
  linarith

theorem abs_R_sub_le {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) {x : ℝ}
    (hx : 2 ≤ x) : |R x - cR / log x| ≤ CR * pntE x / log x := by
  have hl : 0 < log x := log_pos (by linarith)
  rw [show R x - cR / log x = (R x * log x - cR) / log x by field_simp, abs_div,
    abs_of_pos hl]
  exact div_le_div_of_nonneg_right (hR x hx) hl.le

/-- Only `p₁ ≥ y^{1/4}` contribute to `d_{2,y}(s)`, and the inner sum telescopes:
`d_{2,y}(s) = ∑_{y^{1/4} ≤ p₁ < y^{1/s}} (R(y₁^{1/3}) - R(p₁)) / p₁`. -/
theorem d2_eq_sum {y : ℝ} (hy : 1 < y) (s : ℝ) :
    d2 y s = ∑ p₁ ∈ (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ y ^ (1 / (4 : ℝ)) ≤ p),
      (R ((y / p₁) ^ ((1 : ℝ) / 3)) - R p₁) / p₁ := by
  have hy0 : 0 < y := by linarith
  set L := log y
  -- logarithms of the relevant quantities
  have key : ∀ p : ℕ, p.Prime → 0 < log (p : ℝ) ∧
      log ((y / p) ^ ((1 : ℝ) / 3)) = (L - log p) / 3 ∧
      (y ^ (1 / (4 : ℝ)) ≤ p ↔ L / 4 ≤ log p) ∧
      ((y / p) ^ ((1 : ℝ) / 3) ≤ p ↔ L / 4 ≤ log p) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
    have hB1 : log ((y / p) ^ ((1 : ℝ) / 3)) = (L - log p) / 3 := by
      rw [log_rpow_one_div (div_pos hy0 hp0), log_div hy0.ne' hp0.ne']
    refine ⟨hlp, hB1, ?_, ?_⟩
    · rw [← log_le_log_iff (rpow_pos_of_pos hy0 _) hp0, log_rpow_one_div hy0]
    · rw [← log_le_log_iff (rpow_pos_of_pos (div_pos hy0 hp0) _) hp0, hB1]
      constructor <;> intro h <;> linarith
  rw [d2, ← sum_filter_add_sum_filter_not _ (fun p : ℕ ↦ y ^ (1 / (4 : ℝ)) ≤ p)]
  rw [sum_eq_zero (s := (primesLT (y ^ (1 / s))).filter fun p : ℕ ↦ ¬ y ^ (1 / (4 : ℝ)) ≤ p),
    add_zero]
  · refine sum_congr rfl fun p₁ hp₁ ↦ ?_
    obtain ⟨hp₁z, hp₁B⟩ := mem_filter.1 hp₁
    have hp := prime_of_mem_primesLT hp₁z
    obtain ⟨-, -, h1, h2⟩ := key p₁ hp
    rw [← TheoremFour.sum_R_div_eq ((h2.2 (h1.1 hp₁B))), sum_div]
    exact sum_congr rfl fun p₂ _ ↦ by rw [div_div, mul_comm (p₁ : ℝ)]
  · intro p₁ hp₁
    obtain ⟨hp₁z, hp₁B⟩ := mem_filter.1 hp₁
    have hp := prime_of_mem_primesLT hp₁z
    obtain ⟨hl1, hB1, h1, -⟩ := key p₁ hp
    have hlt : log p₁ < L / 4 := not_le.1 fun h ↦ hp₁B (h1.2 h)
    refine sum_eq_zero fun p₂ hp₂ ↦ absurd hp₂ fun hp₂ ↦ ?_
    obtain ⟨hp₂p, hBp₂⟩ := mem_filter.1 hp₂
    have hq := prime_of_mem_primesLT hp₂p
    have hq0 : (0 : ℝ) < p₂ := by exact_mod_cast hq.pos
    have h3 := log_le_log (rpow_pos_of_pos (div_pos hy0 (by exact_mod_cast hp.pos)) _) hBp₂
    have h4 := log_lt_log hq0 (lt_of_mem_primesLT hp₂p)
    rw [hB1] at h3
    linarith

/-- `∫_s^4 (3t/(t-1) - t)/L · dt/t = g₂(s)/L` for `2 ≤ s ≤ 4`. -/
theorem integral_lemma16 {s L : ℝ} (hs : s ∈ Set.Icc (2 : ℝ) 4) :
    ∫ t in s..4, (3 * t / (t - 1) - t) / L / t = g 2 s / L := by
  have hmem : ∀ t ∈ Set.uIcc s 4, 2 ≤ t := fun t ht ↦ by
    rw [Set.uIcc_of_le hs.2] at ht; linarith [ht.1, hs.1]
  have hcongr : ∫ t in s..4, (3 * t / (t - 1) - t) / L / t =
      ∫ t in s..4, (3 / (t - 1) - 1) / L := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have := hmem t ht
    have h1 : t - 1 ≠ 0 := by linarith
    have h2 : t ≠ 0 := by linarith
    field_simp
  rw [hcongr, intervalIntegral.integral_div]
  have hderiv : ∀ t ∈ Set.uIcc s 4,
      HasDerivAt (fun t ↦ 3 * log (t - 1) - t) (3 / (t - 1) - 1) t := fun t ht ↦ by
    have h1 : t - 1 ≠ 0 := by linarith [hmem t ht]
    have h2 : HasDerivAt (fun x : ℝ ↦ x - 1) 1 t := (hasDerivAt_id' t).sub_const 1
    have h4 := ((h2.log h1).const_mul 3).sub (hasDerivAt_id' t)
    convert h4 using 1
    field_simp
  have hcont : ContinuousOn (fun t : ℝ ↦ 3 / (t - 1) - 1) (Set.uIcc s 4) :=
    (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht ↦
      (show (0 : ℝ) < t - 1 by linarith [hmem t ht]).ne').sub continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable),
    g_two_eq hs]
  congr 1
  have h1 : (0 : ℝ) < s - 1 := by linarith [hs.1]
  rw [log_div (by norm_num) h1.ne']
  norm_num
  ring

/-- [I71, Lemma 16]: for `y > 1` and `s ≥ 2`,
`cR⁻¹ d_{2,y}(s) < g₂(s) / log y + c₆ pntE(y^{1/6})`, where `cR` (Iwaniec's `e^{-γ}`) is the
constant of `R(z) log z → cR`. -/
theorem lemma16 {cR CR : ℝ} (hcR : 0 < cR) (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
    ∃ c₆ : ℝ, ∀ y s : ℝ, 1 < y → 2 ≤ s →
      cR⁻¹ * d2 y s < g 2 s / log y + c₆ * pntE (y ^ (1 / (6 : ℝ))) := by
  obtain ⟨C₁₃, hC₁₃, h13⟩ := lemma13_param
  obtain ⟨C₁₄, h14⟩ := lemma14_of_subset
  have hCR : 0 ≤ CR := by
    have h := (abs_nonneg _).trans (hR 2 le_rfl)
    by_contra hneg
    nlinarith [pntE_pos 2]
  have hE2 := pntE_pos 2
  set K := 6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR + (64 / cR + 1) / pntE 2 + 1 with hK
  have hK1 : 6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR + 1 ≤ K := by
    have : 0 ≤ (64 / cR + 1) / pntE 2 := by positivity
    linarith
  have hK2 : (64 / cR + 1) / pntE 2 ≤ K := by
    have : 0 ≤ 4 * CR * (2 + |C₁₄|) / cR := by positivity
    linarith
  have hK0 : 0 < K := by
    have : 0 ≤ 4 * CR * (2 + |C₁₄|) / cR := by positivity
    linarith
  refine ⟨K, fun y s hy hs ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  set L := log y with hL_def
  have hL : 0 < L := log_pos hy
  have hs0 : 0 < s := by linarith
  set E := pntE (y ^ (1 / (6 : ℝ)))
  have hE : 0 < E := pntE_pos _
  have hg : 0 ≤ g 2 s / L := div_nonneg (g_nonneg 2 s) hL.le
  have hlog2 := log_two_gt_d9
  have hlog64 : log (64 : ℝ) = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]; norm_num
  have hlogz : log (y ^ (1 / s)) = L / s := log_rpow_one_div hy0 s
  have hlog6 : log (y ^ (1 / (6 : ℝ))) = L / 6 := log_rpow_one_div hy0 6
  have hlog4 : log (y ^ (1 / (4 : ℝ))) = L / 4 := log_rpow_one_div hy0 4
  have hLs : L / s ≤ L / 2 := div_le_div_of_nonneg_left hL.le two_pos hs
  rcases lt_or_ge y 64 with hy64 | hy64
  · -- small `y`: `d₂ ≤ 64` and `pntE(y^{1/6}) ≥ pntE 2`
    have hL64 : L < 6 * log 2 := hlog64 ▸ log_lt_log hy0 hy64
    have hz8 : y ^ (1 / s) ≤ 8 := by
      rw [← log_le_log_iff (rpow_pos_of_pos hy0 _) (by norm_num), hlogz,
        show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
      push_cast
      linarith
    have hcard : #(primesLT (y ^ (1 / s))) ≤ 8 := by
      refine (card_le_card (primesLT_mono hz8)).trans ?_
      rw [primesLT, Nat.primesBelow, show ⌈(8 : ℝ)⌉₊ = 8 by norm_num]
      exact (card_filter_le _ _).trans (card_range 8).le
    have hd2 : d2 y s ≤ 64 := by
      have : d2 y s ≤ ∑ p₁ ∈ primesLT (y ^ (1 / s)), (8 : ℝ) := by
        refine sum_le_sum fun p₁ hp₁ ↦ ?_
        have hsub : (primesLT p₁).filter (fun p₂ : ℕ ↦ (y / p₁) ^ ((1 : ℝ) / 3) ≤ p₂) ⊆
            primesLT (y ^ (1 / s)) :=
          (filter_subset _ _).trans (primesLT_natCast_subset hp₁)
        calc ∑ p₂ ∈ (primesLT p₁).filter (fun p₂ : ℕ ↦ (y / p₁) ^ ((1 : ℝ) / 3) ≤ p₂),
              R p₂ / (p₁ * p₂)
            ≤ ∑ p₂ ∈ (primesLT p₁).filter (fun p₂ : ℕ ↦ (y / p₁) ^ ((1 : ℝ) / 3) ≤ p₂),
              (1 : ℝ) := by
              refine sum_le_sum fun p₂ hp₂ ↦ ?_
              have h1 : (1 : ℝ) ≤ p₁ := by exact_mod_cast (prime_of_mem_primesLT hp₁).one_le
              have h2 : (1 : ℝ) ≤ p₂ := by
                exact_mod_cast (prime_of_mem_primesLT (mem_filter.1 hp₂).1).one_le
              rw [div_le_one (by positivity)]
              nlinarith [R_le_one (p₂ : ℝ)]
          _ ≤ 8 := by
              rw [sum_const, nsmul_one]
              exact_mod_cast (card_le_card hsub).trans hcard
      refine this.trans ?_
      rw [sum_const, nsmul_eq_mul]
      have : (#(primesLT (y ^ (1 / s))) : ℝ) ≤ 8 := by exact_mod_cast hcard
      nlinarith
    have hE2' : pntE 2 ≤ E := pntE_le_of_log_le (by rw [hlog6]; linarith)
    calc cR⁻¹ * d2 y s ≤ cR⁻¹ * 64 := mul_le_mul_of_nonneg_left hd2 (inv_pos.2 hcR).le
      _ < (64 / cR + 1) / pntE 2 * pntE 2 := by
          rw [div_mul_cancel₀ _ hE2.ne']; rw [inv_mul_eq_div]; linarith
      _ ≤ K * E := mul_le_mul hK2 hE2' hE2.le hK0.le
      _ ≤ g 2 s / L + K * E := by linarith
  -- large `y`
  have hL64 : 6 * log 2 ≤ L := hlog64 ▸ log_le_log (by norm_num) hy64
  rw [d2_eq_sum hy s]
  set B := y ^ (1 / (4 : ℝ))
  set z := y ^ (1 / s)
  set S := (primesLT z).filter (fun p : ℕ ↦ B ≤ p)
  have hB2 : 2 ≤ B := by
    rw [← log_le_log_iff (by norm_num) (rpow_pos_of_pos hy0 _), hlog4]; linarith
  -- facts for `p ∈ S`
  have hSfacts : ∀ p ∈ S, p.Prime ∧ 2 ≤ (p : ℝ) ∧ L / 4 ≤ log p ∧ log p ≤ L / 2 := by
    intro p hp
    obtain ⟨hpz, hpB⟩ := mem_filter.1 hp
    have hpp := prime_of_mem_primesLT hpz
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    refine ⟨hpp, by exact_mod_cast hpp.two_le, ?_, ?_⟩
    · rw [← hlog4]; exact log_le_log (rpow_pos_of_pos hy0 _) hpB
    · have := log_lt_log hp0 (lt_of_mem_primesLT hpz)
      rw [hlogz] at this
      linarith
  rcases lt_or_ge 4 s with hs4 | hs4
  · -- `s > 4`: no `p₁` contributes
    have hS : S = ∅ := by
      refine filter_eq_empty_iff.2 fun p hp hpB ↦ ?_
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
      have h1 := log_lt_log hp0 (lt_of_mem_primesLT hp)
      have h2 := log_le_log (rpow_pos_of_pos hy0 _) hpB
      rw [hlogz] at h1
      rw [hlog4] at h2
      have : L / s < L / 4 := div_lt_div_of_pos_left hL (by norm_num) hs4
      linarith
    rw [hS, sum_empty, mul_zero]
    positivity
  have hsI : s ∈ Set.Icc (2 : ℝ) 4 := ⟨hs, hs4⟩
  -- the main term, by Lemma 13
  set F : ℝ → ℝ := fun t ↦ (3 * t / (t - 1) - t) / L
  have hSsub1 : ∀ p ∈ S, p.Prime ∧ y ^ (1 / (4 : ℝ)) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / s) := fun p hp ↦
    ⟨prime_of_mem_primesLT (mem_filter.1 hp).1, (mem_filter.1 hp).2,
      (lt_of_mem_primesLT (mem_filter.1 hp).1).le⟩
  have hSsub2 : ∀ p : ℕ, p.Prime → y ^ (1 / (4 : ℝ)) < p → (p : ℝ) < y ^ (1 / s) → p ∈ S :=
    fun p hp h1 h2 ↦ mem_filter.2 ⟨mem_primesLT.2 ⟨hp, h2⟩, h1.le⟩
  have hFanti : AntitoneOn F (Set.Icc s 4) := by
    intro u hu v hv huv
    have hu1 : 0 < u - 1 := by linarith [hu.1]
    have hv1 : 0 < v - 1 := by linarith [hv.1]
    simp only [F]
    refine div_le_div_of_nonneg_right ?_ hL.le
    have : 3 * v / (v - 1) ≤ 3 * u / (u - 1) := by
      rw [div_le_div_iff₀ hv1 hu1]; nlinarith
    linarith
  have hF0 : ∀ t ∈ Set.Icc s 4, 0 ≤ F t := by
    intro t ht
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    simp only [F]
    refine div_nonneg ?_ hL.le
    rw [sub_nonneg, le_div_iff₀ ht1]
    nlinarith [ht.2]
  have hFs : F s ≤ 6 := by
    have hs1 : 0 < s - 1 := by linarith
    simp only [F]
    rw [div_le_iff₀ hL]
    have : 3 * s / (s - 1) ≤ 6 := by rw [div_le_iff₀ hs1]; linarith
    nlinarith
  have h13' := h13 F y s 4 S hy hs0 hs4 hB2 hFanti hF0 hSsub1 hSsub2
  rw [integral_lemma16 hsI] at h13'
  have hEB : pntE B ≤ E := pntE_le_of_log_le (by rw [hlog6, hlog4]; linarith)
  have hmain : cR * ∑ p ∈ S, F (L / log p) / p ≤ cR * (g 2 s / L + 6 * C₁₃ * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hcR.le
    have h1 := (abs_le.1 h13').2
    have h2 : C₁₃ * F s * pntE B ≤ 6 * C₁₃ * E := by
      calc C₁₃ * F s * pntE B ≤ C₁₃ * 6 * E :=
            mul_le_mul (mul_le_mul_of_nonneg_left hFs hC₁₃) hEB (pntE_pos _).le (by positivity)
        _ = 6 * C₁₃ * E := by ring
    linarith
  -- the error terms
  have hterm : ∀ p ∈ S, |(R ((y / p) ^ ((1 : ℝ) / 3)) - R p) / p - cR * (F (L / log p) / p)| ≤
      4 * CR * E * (1 / (p * log p)) := by
    intro p hp
    obtain ⟨hpp, hp2, hlp1, hlp2⟩ := hSfacts p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 < log (p : ℝ) := by linarith
    set B₁ := (y / p) ^ ((1 : ℝ) / 3)
    have hB₁0 : 0 < B₁ := rpow_pos_of_pos (div_pos hy0 hp0) _
    have hlB₁ : log B₁ = (L - log p) / 3 := by
      rw [log_rpow_one_div (div_pos hy0 hp0), log_div hy0.ne' hp0.ne']
    have hB₁2 : 2 ≤ B₁ := by
      rw [← log_le_log_iff (by norm_num) hB₁0, hlB₁]; linarith
    have hlB₁0 : 0 < log B₁ := by rw [hlB₁]; linarith
    have hF : cR * F (L / log p) = cR / log B₁ - cR / log p := by
      simp only [F]
      rw [hlB₁]
      have h1 : L - log p ≠ 0 := by linarith
      have h2 : L / log p - 1 ≠ 0 := by
        rw [div_sub_one hlp.ne']; exact div_ne_zero h1 hlp.ne'
      field_simp
    have e1 := abs_R_sub_le hR hB₁2
    have e2 := abs_R_sub_le hR hp2
    have hE1 : pntE B₁ ≤ E := pntE_le_of_log_le (by rw [hlog6, hlB₁]; linarith)
    have hE2 : pntE p ≤ E := pntE_le_of_log_le (by rw [hlog6]; linarith)
    have e1' : CR * pntE B₁ / log B₁ ≤ 3 * CR * E / log p := by
      rw [div_le_div_iff₀ hlB₁0 hlp, hlB₁]
      have h1 : CR * pntE B₁ ≤ CR * E := mul_le_mul_of_nonneg_left hE1 hCR
      have h2 : 0 ≤ CR * E := mul_nonneg hCR hE.le
      calc CR * pntE B₁ * log p ≤ CR * E * log p := mul_le_mul_of_nonneg_right h1 hlp.le
        _ ≤ CR * E * (L - log p) := mul_le_mul_of_nonneg_left (by linarith) h2
        _ = 3 * CR * E * ((L - log p) / 3) := by ring
    have e2' : CR * pntE p / log p ≤ CR * E / log p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE2 hCR) hlp.le
    have heq : (R B₁ - R p) / p - cR * (F (L / log p) / p) =
        ((R B₁ - cR / log B₁) - (R p - cR / log p)) / p := by
      rw [← mul_div_assoc, hF]; ring
    have habs : |R B₁ - cR / log B₁ - (R p - cR / log p)| ≤ 4 * CR * E / log p := by
      refine (abs_sub _ _).trans ?_
      have : 4 * CR * E / log p = 3 * CR * E / log p + CR * E / log p := by ring
      rw [this]
      exact add_le_add (e1.trans e1') (e2.trans e2')
    rw [heq, abs_div, abs_of_pos hp0]
    calc |R B₁ - cR / log B₁ - (R p - cR / log p)| / p ≤ 4 * CR * E / log p / p :=
          div_le_div_of_nonneg_right habs hp0.le
      _ = 4 * CR * E * (1 / (p * log p)) := by field_simp
  have h14' := h14 z B S hB2 (rpow_le_rpow_of_exponent_le hy.le
    (one_div_le_one_div_of_le hs0 hs4)) hSsub1 hSsub2
  have hsum14 : ∑ p ∈ S, 1 / ((p : ℝ) * log p) ≤ 2 + |C₁₄| := by
    have h1 := (abs_le.1 h14').2
    have hlB : 1 / log B ≤ 1 := by
      rw [hlog4, one_div_le (by linarith) one_pos]; linarith
    have hlz : 0 ≤ 1 / log z := by
      rw [hlogz]; exact div_nonneg zero_le_one (div_nonneg hL.le hs0.le)
    have : C₁₄ * pntE B ≤ |C₁₄| := by
      calc C₁₄ * pntE B ≤ |C₁₄| * pntE B :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (pntE_pos _).le
        _ ≤ |C₁₄| * 1 := mul_le_mul_of_nonneg_left (pntE_le_one B) (abs_nonneg _)
        _ = |C₁₄| := mul_one _
    linarith
  have herr : ∑ p ∈ S, (R ((y / p) ^ ((1 : ℝ) / 3)) - R p) / p ≤
      cR * ∑ p ∈ S, F (L / log p) / p + 4 * CR * E * (2 + |C₁₄|) := by
    rw [mul_sum, ← sub_le_iff_le_add', ← sum_sub_distrib]
    refine (sum_le_sum fun p hp ↦ (le_abs_self _).trans (hterm p hp)).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hsum14 (by positivity)
  have hfinal : ∑ p ∈ S, (R ((y / p) ^ ((1 : ℝ) / 3)) - R p) / p ≤
      cR * (g 2 s / L + (6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR) * E) := by
    have : cR * (g 2 s / L + (6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR) * E) =
        cR * (g 2 s / L + 6 * C₁₃ * E) + 4 * CR * E * (2 + |C₁₄|) := by
      field_simp
      ring
    rw [this]
    linarith
  rw [inv_mul_lt_iff₀ hcR]
  calc _ ≤ cR * (g 2 s / L + (6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR) * E) := hfinal
    _ < cR * (g 2 s / L + K * E) := by
        refine mul_lt_mul_of_pos_left ?_ hcR
        have : (6 * C₁₃ + 4 * CR * (2 + |C₁₄|) / cR) * E < K * E :=
          mul_lt_mul_of_pos_right (by linarith) hE
        linarith

/-- [I71, Lemma 16] for the depth-two deficit `fail true 2 y (y^{1/s}) = d_{2,y}(s)`. -/
theorem lemma16_fail {cR CR : ℝ} (hcR : 0 < cR)
    (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
    ∃ c₆ : ℝ, ∀ y s : ℝ, 1 < y → 2 ≤ s →
      cR⁻¹ * fail true 2 y (y ^ (1 / s)) < g 2 s / log y + c₆ * pntE (y ^ (1 / (6 : ℝ))) := by
  obtain ⟨c₆, h⟩ := lemma16 hcR hR
  refine ⟨c₆, fun y s hy hs ↦ ?_⟩
  rw [← d2_eq_fail (by linarith) s]
  exact h y s hy hs

end IwaniecLinearSieve
