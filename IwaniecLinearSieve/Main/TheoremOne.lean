module

public import IwaniecLinearSieve.Main.Basic

@[expose] public section

/-!
# [I71, Theorem 1]

Notation: `L = log y`, `z = y^{1/s}`, `ξ(y) = L / (log log 3y)^{11/5}` (`xi`),
`δ(s, y) = (1 + s² log⁵ s / L²)^{5s}` (`delta`).

**Theorem 1.** Let `y > 1`, `s ≤ ξ(y)`, and assume `(*)`: `|M_d - y/d| ≤ 1` for squarefree `d` with `(d, k) = 1`.
There is an absolute constant `c₀` such that

* (1.1) `A_k(M; y^{1/s}) < y R_k(y^{1/s}) (1 + F(s)/s + c₀ δ(s, y) 𝔐(s) log log 3k / L)`
  for `s ≥ 3`;
* (1.2) `A_k(M; y^{1/s}) > y R_k(y^{1/s}) (1 - f(s)/s - c₀ δ(s, y) 𝔐(s) log log 3k / L)`
  for `s ≥ 2`.

Proof ([I71, §5]). By (2.7), (2.8) with Lemma 2 and (2.12), (2.13) (`siftedCount_le_fail`,
`fail_le_siftedCount`, at a depth `r > π(z)`),

    A ≤ y R_k(z) (1 + fail false r y z / R(z)) + #D⁺,
    A ≥ y R_k(z) (1 - fail true r y z / R(z)) - #D⁻.

For `y ≥ y₀` (so that `z ≥ 2`):

* Theorem 4 gives `fail ≤ cR (M(s)/L + c₇ δ G(s)/L²)`, and Mertens' formula with the PNT error
  gives `cR / R(z) ≤ log z (1 + K pntE z)` with `log z = L/s`; since `pntE z log z ≤ 2/κ²`, the
  error `K pntE(z) M(s)/s` is `≪ M(s)/L ≤ 4𝔐(s)/L` (Lemma 7), so
  `fail / R(z) ≤ M(s)/s + C₁ δ 𝔐(s)/L` (`exists_fail_div_R_le`), where `G ≤ 2𝔐/3` (Corollary to
  Lemma 6);
* Theorem 5 (at depth `π(z)`, where the depth condition is void) gives
  `#D^± ≪ δ G(s) y / L²`, and `R_k(z) ≥ R(z) ≫ 1/log z = s/L ≥ 1/L`, so
  `#D^± ≤ y R_k(z) · C₂ δ 𝔐(s)/L` (`exists_card_rosserSet_le`).

For `1 < y < y₀` both inequalities are trivial once `C` is large: `s ≤ ξ(y) ≤ Ξ` is bounded,
so `𝔐(s) ≥ 𝔐(Ξ)`, `R_k(z) ≥ R(y₀)`, `L ≤ log y₀`, and `A ≤ y + 1 < 2y`.

This proves Theorem 1 in the form `theorem1_core`, with `M(s) = F(s) + (3 - s)⁺` in the upper
bound (valid for `1 ≤ s`), with `≤` in the hypothesis `s ≤ ξ(y)` (the paper has `<`), and
**without** the factor `log log 3k`: [I71] bounds `1/R_k(z) < (k/φ(k)) / R(z)`, but since
`R(z) ≤ R_k(z)` one has the better bound `1/R_k(z) ≤ 1/R(z)`, and then `k` does not enter the
error at all. The form with `log log 3k` (`theorem1`) follows since
`log log 3k ≥ log log 3 > 0`.
-/

open Real Finset Filter

namespace IwaniecLinearSieve

namespace Main

/-- The main-term part of [I71, §5]: for `y ≥ y₀` and `sMin ≤ s ≤ ξ(y)`, `z = y^{1/s} ≥ 2` and
`fail / R(z) ≤ M(s)/s + C₁ δ(s, y) 𝔐(s) / log y`, by Theorem 4 and Mertens' formula. -/
theorem exists_fail_div_R_le : ∃ C₁ y₀ : ℝ, 0 ≤ C₁ ∧ 1 < y₀ ∧
    ∀ (r : ℕ) (lower : Bool) (y s : ℝ), y₀ ≤ y → sMin lower ≤ s → s ≤ xi y →
      2 ≤ y ^ (1 / s) ∧ fail lower r y (y ^ (1 / s)) / R (y ^ (1 / s)) ≤
        mainMaj lower s / s + C₁ * delta s y * bigM s / log y := by
  obtain ⟨cR, hcR, CR, hR⟩ := R_asymp
  obtain ⟨c₇, hc₇, h4⟩ := theorem4 hcR hR
  obtain ⟨K, hK, hKR⟩ := exists_cR_div_R_le hR
  obtain ⟨y₀, hy₀⟩ := exists_xi_large
  set CE := 2 / pntκ ^ 2 with hCE
  have hCE0 : 0 ≤ CE := by positivity
  refine ⟨4 * K * CE + (1 + K) * c₇, max y₀ 2, by positivity,
    lt_of_lt_of_le one_lt_two (le_max_right _ _), fun r lower y s hy hs hsξ => ?_⟩
  obtain ⟨hy1, -, -, hw⟩ := hy₀ y (le_trans (le_max_left _ _) hy)
  have hs1 : 1 ≤ s := (TheoremFour.one_le_sMin lower).trans hs
  have hs0 : 0 < s := by linarith
  have hL : 0 < log y := log_pos hy1
  have hz : 2 ≤ y ^ (1 / s) := hw.trans (rpow_one_div_le_rpow_one_div hy1.le hs0 hsξ)
  refine ⟨hz, ?_⟩
  have hlz : log (y ^ (1 / s)) = log y / s := log_rpow_one_div (by linarith) s
  have hf := h4 r lower y s hy1 hs hsξ
  have hRz := R_pos (y ^ (1 / s))
  have hKRz := hKR _ hz
  have hpl := pntE_mul_log_le (by linarith : (1 : ℝ) ≤ y ^ (1 / s))
  have hp0 := pntE_nonneg (y ^ (1 / s))
  have hp1 := pntE_le_one (y ^ (1 / s))
  set z := y ^ (1 / s)
  set p := pntE z
  set m := mainMaj lower s
  set δ := delta s y
  set G := errMaj lower s
  set B := bigM s
  have hm0 : 0 ≤ m := mainMaj_nonneg _ _
  have hm4 : m ≤ 4 * B := mainMaj_le_four_mul_bigM lower hs
  have hδ1 : 1 ≤ δ := TheoremFour.one_le_delta hs1 y
  have hG0 : 0 ≤ G := (errMaj_pos lower s).le
  have hGB : G ≤ B := by linarith [(errMaj_mem lower s).2, bigM_pos s]
  have hB0 : 0 < B := bigM_pos s
  have hρ0 : (0 : ℝ) ≤ (r : ℝ) / (r + 1) := by positivity
  have hρ1 : (r : ℝ) / (r + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  clear_value z p m δ G B
  set X := m / log y + c₇ * δ * G / log y ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hfX : fail lower r y z ≤ cR * X := by
    refine hf.trans (mul_le_mul_of_nonneg_left ?_ hcR.le)
    rw [hX]
    gcongr
    exact mul_le_of_le_one_right hc₇ hρ1
  have e1 : log z * X = m / s + c₇ * δ * G / (s * log y) := by
    rw [hlz, hX]; field_simp
  have e2 : p * log z * X = p * log z * m / log y + p * (c₇ * δ * G / (s * log y)) := by
    rw [mul_assoc, e1, hlz]; field_simp
  have b1 : p * log z * m / log y ≤ CE * (4 * δ * B) / log y := by
    gcongr
    · nlinarith
  have b2 : p * (c₇ * δ * G / (s * log y)) ≤ c₇ * δ * B / log y := by
    calc p * (c₇ * δ * G / (s * log y)) ≤ 1 * (c₇ * δ * B / (1 * log y)) := by gcongr
      _ = c₇ * δ * B / log y := by ring
  have b3 : c₇ * δ * G / (s * log y) ≤ c₇ * δ * B / log y := by
    calc c₇ * δ * G / (s * log y) ≤ c₇ * δ * B / (1 * log y) := by gcongr
      _ = c₇ * δ * B / log y := by ring
  calc fail lower r y z / R z ≤ cR * X / R z := div_le_div_of_nonneg_right hfX hRz.le
    _ = cR / R z * X := by ring
    _ ≤ log z * (1 + K * p) * X := mul_le_mul_of_nonneg_right hKRz hX0
    _ = log z * X + K * (p * log z * X) := by ring
    _ ≤ m / s + c₇ * δ * B / log y + K * (CE * (4 * δ * B) / log y + c₇ * δ * B / log y) := by
        rw [e1, e2]; gcongr
    _ = m / s + (4 * K * CE + (1 + K) * c₇) * δ * B / log y := by ring

/-- The remainder part of [I71, §5]: by Theorem 5 and `R_k(z) ≥ R(z) ≫ s / log y`,
`#D^± ≤ y R_k(z) · C₂ δ(s, y) 𝔐(s) / log y`. -/
theorem exists_card_rosserSet_le : ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (k : ℕ) (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s → s ≤ xi y → 2 ≤ y ^ (1 / s) →
      (#(rosserSet lower y (y ^ (1 / s))) : ℝ) ≤
        y * Rk k (y ^ (1 / s)) * (C₂ * delta s y * bigM s / log y) := by
  obtain ⟨c₇, hc₇, h5⟩ := theorem5
  obtain ⟨c, hc, hcR⟩ := R_lower
  refine ⟨c₇ / c, by positivity, fun k lower y s hy hs hsξ hz => ?_⟩
  have hs1 : 1 ≤ s := (TheoremFour.one_le_sMin lower).trans hs
  have hs0 : 0 < s := by linarith
  have hL : 0 < log y := log_pos hy
  have hlz : log (y ^ (1 / s)) = log y / s := log_rpow_one_div (by linarith) s
  have h := h5 (#(primesLT (y ^ (1 / s)))) lower y s hy hs hsξ
  rw [filter_true_of_mem fun d hd => card_primeFactors_le_card_primesLT hd] at h
  have hRz := hcR _ hz
  rw [hlz] at hRz
  have hRk := R_le_Rk k (y ^ (1 / s))
  have hδ1 : 1 ≤ delta s y := TheoremFour.one_le_delta hs1 y
  have hGB : errMaj lower s ≤ bigM s := by linarith [(errMaj_mem lower s).2, bigM_pos s]
  have hG0 : 0 ≤ errMaj lower s := (errMaj_pos lower s).le
  set ρ := ((#(primesLT (y ^ (1 / s))) : ℝ) + 1) / (#(primesLT (y ^ (1 / s))) + 2)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hRL : c / log y ≤ Rk k (y ^ (1 / s)) := by
    refine le_trans ?_ (hRz.trans hRk)
    rw [div_div_eq_mul_div]
    gcongr
    nlinarith
  have hB0 := (bigM_pos s).le
  have hy0 : 0 ≤ y := by linarith
  calc (#(rosserSet lower y (y ^ (1 / s))) : ℝ)
      ≤ c₇ * ρ * delta s y * errMaj lower s * y / log y ^ 2 := h
    _ ≤ c₇ * 1 * delta s y * bigM s * y / log y ^ 2 := by gcongr
    _ = y * (c / log y) * (c₇ / c * delta s y * bigM s / log y) := by field_simp
    _ ≤ y * Rk k (y ^ (1 / s)) * (c₇ / c * delta s y * bigM s / log y) := by gcongr

end Main

open Main

/-- **[I71, Theorem 1]**, the form proved in [I71, §5], uniform in `k` and without the factor
`log log 3k` (see the module docstring): for `y > 1`, `s ≤ ξ(y)` and `(*)`,

* `A_k(M; y^{1/s}) ≤ y R_k(y^{1/s}) (1 + (F(s) + (3 - s)⁺)/s + C δ(s, y) 𝔐(s)/log y)` for `s ≥ 1`;
* `A_k(M; y^{1/s}) ≥ y R_k(y^{1/s}) (1 - f(s)/s - C δ(s, y) 𝔐(s)/log y)` for `s ≥ 2`. -/
theorem theorem1_core : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (M : Multiset ℤ) (y s : ℝ), 1 < y →
    (∀ d : ℕ, Squarefree d → d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → s ≤ xi y →
    (1 ≤ s → (siftedCount k M (y ^ (1 / s)) : ℝ) ≤
      y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s + C * delta s y * bigM s / log y)) ∧
    (2 ≤ s → y * Rk k (y ^ (1 / s)) * (1 - fSieve s / s - C * delta s y * bigM s / log y) ≤
      siftedCount k M (y ^ (1 / s))) := by
  obtain ⟨C₁, y₀, hC₁, hy₀, hfail⟩ := exists_fail_div_R_le
  obtain ⟨C₂, hC₂, hcard⟩ := exists_card_rosserSet_le
  set Ξ := log y₀ / log (log 3) ^ (11 / 5 : ℝ)
  have hL₀ : 0 < log y₀ := log_pos hy₀
  set C₀ := 2 * log y₀ / (R y₀ * bigM Ξ)
  have hC₀ : 0 ≤ C₀ := by have := R_pos y₀; have := bigM_pos Ξ; positivity
  refine ⟨C₁ + C₂ + C₀, by positivity, fun k M y s hy hM hsξ => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 ≤ y := by linarith
  -- the small range `y < y₀`
  have small : y < y₀ → 1 ≤ s →
      2 * y ≤ y * Rk k (y ^ (1 / s)) * ((C₁ + C₂ + C₀) * delta s y * bigM s / log y) ∧
      2 ≤ (C₁ + C₂ + C₀) * delta s y * bigM s / log y := by
    intro hyy hs1
    have hδ1 : 1 ≤ delta s y := TheoremFour.one_le_delta hs1 y
    have hsΞ : s ≤ Ξ := hsξ.trans (TheoremFive.xi_le_of_lt hy hyy)
    have hBΞ : bigM Ξ ≤ bigM s := bigM_antitone hsΞ
    have hBΞ0 := bigM_pos Ξ
    have hRy₀ := R_pos y₀
    have hR1 : R y₀ ≤ 1 := R_le_one y₀
    have hRk : R y₀ ≤ Rk k (y ^ (1 / s)) :=
      (R_antitone ((rpow_one_div_le_self hy.le hs1).trans hyy.le)).trans (R_le_Rk k _)
    have hLL : log y ≤ log y₀ := log_le_log (by linarith) hyy.le
    have n1 : C₀ * bigM Ξ ≤ (C₁ + C₂ + C₀) * delta s y * bigM s := by
      have : bigM Ξ ≤ delta s y * bigM s := by nlinarith
      calc C₀ * bigM Ξ ≤ (C₁ + C₂ + C₀) * bigM Ξ := by gcongr; linarith
        _ ≤ (C₁ + C₂ + C₀) * (delta s y * bigM s) := by gcongr
        _ = (C₁ + C₂ + C₀) * delta s y * bigM s := by ring
    have h1 : 2 / R y₀ ≤ (C₁ + C₂ + C₀) * delta s y * bigM s / log y := by
      calc 2 / R y₀ = C₀ * bigM Ξ / log y₀ := by
            simp only [C₀]; field_simp
        _ ≤ (C₁ + C₂ + C₀) * delta s y * bigM s / log y :=
            div_le_div₀ (le_trans (by positivity) n1) n1 hL hLL
    have h2 : 2 ≤ 2 / R y₀ := by rw [le_div_iff₀ hRy₀]; linarith
    refine ⟨?_, h2.trans h1⟩
    calc 2 * y = y * R y₀ * (2 / R y₀) := by field_simp
      _ ≤ y * Rk k (y ^ (1 / s)) * ((C₁ + C₂ + C₀) * delta s y * bigM s / log y) := by
          gcongr
          exact mul_nonneg hy0 (Rk_nonneg k _)
  have hRk0 := Rk_pos k (y ^ (1 / s))
  have hyRk : 0 < y * Rk k (y ^ (1 / s)) := mul_pos (by linarith) hRk0
  constructor
  · intro hs1
    have hs0 : 0 < s := by linarith
    have hm : 0 ≤ mainMaj false s / s := div_nonneg (mainMaj_nonneg false s) hs0.le
    rcases lt_or_ge y y₀ with hyy | hyy
    · -- trivial: `A ≤ y + 1 < 2y`
      have hA := siftedCount_le_add_one (z := y ^ (1 / s)) hM
      have h := (small hyy hs1).1
      have : 0 ≤ y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s) := by positivity
      nlinarith
    · obtain ⟨hz, hf⟩ := hfail (#(primesLT (y ^ (1 / s))) + 1) false y s hyy hs1 hsξ
      have hA := siftedCount_le_fail (k := k) hy0 hM
        (Nat.lt_succ_self (#(primesLT (y ^ (1 / s)))))
      have hc := hcard k false y s hy hs1 hsξ hz
      have hδB : 0 ≤ delta s y * bigM s / log y :=
        div_nonneg (mul_nonneg (TheoremFour.one_le_delta hs1 y |>.trans' zero_le_one)
          (bigM_pos s).le) hL.le
      calc (siftedCount k M (y ^ (1 / s)) : ℝ)
          ≤ y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s + C₁ * delta s y * bigM s / log y)
            + y * Rk k (y ^ (1 / s)) * (C₂ * delta s y * bigM s / log y) := by
            refine hA.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hyRk.le) hc)
            simp only [Nat.succ_eq_add_one] at hf ⊢
            linarith
        _ = y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s +
              (C₁ + C₂) * (delta s y * bigM s / log y)) := by ring
        _ ≤ y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s +
              (C₁ + C₂ + C₀) * (delta s y * bigM s / log y)) := by
            exact mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hC₀ hδB]) hyRk.le
        _ = y * Rk k (y ^ (1 / s)) * (1 + mainMaj false s / s +
              (C₁ + C₂ + C₀) * delta s y * bigM s / log y) := by ring
  · intro hs2
    have hs1 : (1 : ℝ) ≤ s := by linarith
    have hs0 : 0 < s := by linarith
    have hf0 : 0 ≤ fSieve s / s := div_nonneg (fSieve_nonneg s) hs0.le
    rcases lt_or_ge y y₀ with hyy | hyy
    · -- trivial: the bracket is negative
      have h := (small hyy hs1).2
      have : y * Rk k (y ^ (1 / s)) *
          (1 - fSieve s / s - (C₁ + C₂ + C₀) * delta s y * bigM s / log y) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hyRk.le (by linarith)
      exact this.trans (Nat.cast_nonneg _)
    · obtain ⟨hz, hf⟩ := hfail (#(primesLT (y ^ (1 / s))) + 1) true y s hyy hs2 hsξ
      have hA := fail_le_siftedCount (k := k) hy0 hM
        (Nat.lt_succ_self (#(primesLT (y ^ (1 / s)))))
      have hc := hcard k true y s hy hs2 hsξ hz
      have hδB : 0 ≤ delta s y * bigM s / log y :=
        div_nonneg (mul_nonneg (TheoremFour.one_le_delta hs1 y |>.trans' zero_le_one)
          (bigM_pos s).le) hL.le
      refine le_trans ?_ hA
      calc y * Rk k (y ^ (1 / s)) *
            (1 - fSieve s / s - (C₁ + C₂ + C₀) * delta s y * bigM s / log y)
          = y * Rk k (y ^ (1 / s)) * (1 - fSieve s / s -
              (C₁ + C₂ + C₀) * (delta s y * bigM s / log y)) := by ring
        _ ≤ y * Rk k (y ^ (1 / s)) * (1 - fSieve s / s -
              (C₁ + C₂) * (delta s y * bigM s / log y)) := by
            exact mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hC₀ hδB]) hyRk.le
        _ = y * Rk k (y ^ (1 / s)) * (1 - (fSieve s / s + C₁ * delta s y * bigM s / log y))
            - y * Rk k (y ^ (1 / s)) * (C₂ * delta s y * bigM s / log y) := by ring
        _ ≤ y * Rk k (y ^ (1 / s)) * (1 - fail true (#(primesLT (y ^ (1 / s))) + 1) y
              (y ^ (1 / s)) / R (y ^ (1 / s))) - #(rosserSet true y (y ^ (1 / s))) := by
            refine sub_le_sub (mul_le_mul_of_nonneg_left ?_ hyRk.le) hc
            rw [mainMaj_true] at hf
            linarith

/-- `C δ 𝔐 / L < c₀ δ 𝔐 log log 3k / L` for `c₀ = (C + 1) / log log 3`. -/
theorem lt_loglog_err {C y s : ℝ} (hC : 0 ≤ C) (hy : 1 < y) (hs : 1 ≤ s) {k : ℕ} (hk : 1 ≤ k) :
    C * delta s y * bigM s / log y <
      (C + 1) / log (log 3) * delta s y * bigM s * log (log (3 * k)) / log y := by
  have ha := loglog_three_pos
  have hk3 := loglog_three_le hk
  have hL := log_pos hy
  have hδB : 0 < delta s y * bigM s := mul_pos (delta_pos hs y) (bigM_pos s)
  have h1 : C < (C + 1) / log (log 3) * log (log (3 * k)) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ ha]; nlinarith
  rw [div_lt_div_iff_of_pos_right hL]
  calc C * delta s y * bigM s = C * (delta s y * bigM s) := by ring
    _ < (C + 1) / log (log 3) * log (log (3 * k)) * (delta s y * bigM s) := by gcongr
    _ = (C + 1) / log (log 3) * delta s y * bigM s * log (log (3 * k)) := by ring

/-- **[I71, Theorem 1]**, (1.1) and (1.2), with the error term as printed (with `log log 3k`).
Let `y > 1`, `s ≤ ξ(y) = log y / (log log 3y)^{11/5}`, and assume `(*)`:
`|M_d - y/d| ≤ 1` for all squarefree `d` coprime to `k`. There is an absolute constant `c₀` such that

* (1.1) `A_k(M; y^{1/s}) < y R_k(y^{1/s}) (1 + F(s)/s + c₀ δ(s, y) 𝔐(s) log log 3k / log y)`
  for `s ≥ 3`;
* (1.2) `A_k(M; y^{1/s}) > y R_k(y^{1/s}) (1 - f(s)/s - c₀ δ(s, y) 𝔐(s) log log 3k / log y)`
  for `s ≥ 2`,

where `δ(s, y) = (1 + s² log⁵ s / log² y)^{5s}`.

[I71] assumes `s < ξ(y)`; we allow `s ≤ ξ(y)`. The factor `log log 3k` is not needed
(`theorem1_core`). -/
theorem theorem1 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y s : ℝ), 1 < y →
    (∀ d : ℕ, Squarefree d → d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) →
    s ≤ log y / log (log (3 * y)) ^ (11 / 5 : ℝ) →
    (3 ≤ s → (siftedCount k M (y ^ (1 / s)) : ℝ) < y * Rk k (y ^ (1 / s)) *
      (1 + FSieve s / s + c₀ * (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s) * bigM s *
        log (log (3 * k)) / log y)) ∧
    (2 ≤ s → y * Rk k (y ^ (1 / s)) * (1 - fSieve s / s - c₀ *
      (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s) * bigM s * log (log (3 * k)) / log y) <
      siftedCount k M (y ^ (1 / s))) := by
  obtain ⟨C, hC, h⟩ := theorem1_core
  refine ⟨(C + 1) / log (log 3), by have := loglog_three_pos; positivity,
    fun k hk M y s hy hM hsξ => ?_⟩
  rw [show (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s) = delta s y from rfl]
  obtain ⟨h1, h2⟩ := h k M y s hy hM hsξ
  have hyRk : 0 < y * Rk k (y ^ (1 / s)) := mul_pos (by linarith) (Rk_pos k _)
  constructor
  · intro hs3
    have hA := h1 (by linarith)
    rw [mainMaj_false_of_three_le hs3] at hA
    refine hA.trans_lt (mul_lt_mul_of_pos_left ?_ hyRk)
    linarith [lt_loglog_err hC hy (by linarith : (1 : ℝ) ≤ s) hk]
  · intro hs2
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ?_ hyRk) (h2 hs2)
    linarith [lt_loglog_err hC hy (by linarith : (1 : ℝ) ≤ s) hk]

end IwaniecLinearSieve
