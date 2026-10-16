import IwaniecLinearSieve.General.RosserK
import IwaniecLinearSieve.General.Totient
import IwaniecLinearSieve.LinearSieve.TheoremFour
import IwaniecLinearSieve.LinearSieve.TheoremFive
import IwaniecLinearSieve.LinearSieve.LemmaSeven
import IwaniecLinearSieve.SieveMajorants.Asymptotic

/-!
# Preliminaries for [I71, §5]

* (2.7), (2.8) with Lemma 2 and (2.12), (2.13), with the level `D` of Rosser's sieve separate
  from the density `y` of `(*)` (`siftedCount_le_fail_of_level`, `fail_le_siftedCount_of_level`);
  [I71] always takes `D = y`, but the fundamental lemma below uses a smaller level.
* Trivial bounds: `A_k(M; z) ≤ y + 1` (from `(*)` with `d = 1`), `R_k ≤ 1`, hence
  `|A_k(M; z) - y R_k(z)| ≤ 2y` for `y ≥ 1`.
* `pntE z · log z ≤ 2/κ²`; `M(s) ≤ 4 𝔐(s)` on the whole range `s ≥ sMin` (Lemma 7, and
  `F(3) + 3 - s < 3 = 𝔐(s)` for `1 ≤ s ≤ 2`); `cR / R(z) ≤ log z (1 + K pntE z)` (Mertens with the
  PNT error, in the form `1/R(y^{1/s}) = log y/(cR s) (1 + O(pntE))`).
-/

open Real Finset Filter

namespace IwaniecLinearSieve

variable {k : ℕ} {M : Multiset ℤ} {y D z : ℝ}

/-- (2.7), Lemma 2 and (2.12) for Rosser's sieve of level `D` applied to a sequence of density
`y`: under `(*)`, for `r > π(z)`,
`A_k(M; z) ≤ y R_k(z) (1 + fail false r D z / R(z)) + #D⁺(D, z)`. -/
theorem siftedCount_le_fail_of_level (hy : 0 ≤ y) (hD : 0 ≤ D)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) {r : ℕ}
    (hr : #(primesLT z) < r) :
    (siftedCount k M z : ℝ) ≤
      y * Rk k z * (1 + fail false r D z / R z) + #(rosserSet false D z) := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) := by omega
  have h1 := lemma1_cor_upper (f := rosserTrunc D) (even_two_mul (#(primesLT z))) [] hM z
  rw [truncMain_rosserTrunc hD k false hn, truncSet_rosserTrunc_of_card_le hD k false hn] at h1
  have h2 := mul_le_mul_of_nonneg_left (rosserMainK_false_le_fail hD k hr) hy
  have h3 : (#((rosserSet false D z).filter (·.Coprime k)) : ℝ) ≤ #(rosserSet false D z) := by
    exact_mod_cast card_filter_le _ _
  rw [← mul_assoc] at h2
  linarith

/-- (2.8), Lemma 2 and (2.13) for Rosser's sieve of level `D` applied to a sequence of density
`y`: under `(*)`, for `r > π(z)`,
`A_k(M; z) ≥ y R_k(z) (1 - fail true r D z / R(z)) - #D⁻(D, z)`. -/
theorem fail_le_siftedCount_of_level (hy : 0 ≤ y) (hD : 0 ≤ D)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) {r : ℕ}
    (hr : #(primesLT z) < r) :
    y * Rk k z * (1 - fail true r D z / R z) - #(rosserSet true D z) ≤
      (siftedCount k M z : ℝ) := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) + 1 := by omega
  have h1 := lemma1_cor_lower (f := rosserTrunc D) (odd_two_mul_add_one (#(primesLT z))) [] hM z
  rw [truncMain_rosserTrunc hD k true hn, truncSet_rosserTrunc_of_card_le hD k true hn] at h1
  have h2 := mul_le_mul_of_nonneg_left (le_rosserMainK_true_fail hD k hr) hy
  have h3 : (#((rosserSet true D z).filter (·.Coprime k)) : ℝ) ≤ #(rosserSet true D z) := by
    exact_mod_cast card_filter_le _ _
  rw [← mul_assoc] at h2
  linarith

/-- Under `(*)`, `A_k(M; z) ≤ |M| ≤ y + 1` (take `d = 1`). -/
theorem siftedCount_le_add_one
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    (siftedCount k M z : ℝ) ≤ y + 1 := by
  have h1 := (abs_le.1 (hM 1 (Nat.coprime_one_left k))).2
  have h2 : siftedCount k M z ≤ multiplesCount M 1 := by
    unfold siftedCount multiplesCount
    calc _ ≤ Multiset.card M := Multiset.countP_le_card _ _
      _ = _ := by rw [Multiset.countP_eq_card.2 fun a _ ↦ by simp]
  have h2' : (siftedCount k M z : ℝ) ≤ multiplesCount M 1 := by exact_mod_cast h2
  simp only [Nat.cast_one, div_one] at h1
  linarith

theorem Rk_le_one (k : ℕ) (z : ℝ) : Rk k z ≤ 1 :=
  prod_le_one₀ (fun _ hp ↦ (one_sub_inv_pos (prime_of_mem_primesLTk hp)).le)
    fun p _ ↦ one_sub_inv_le_one p

/-- The trivial bound `|A_k(M; z) - y R_k(z)| ≤ 2y` under `(*)`, for `y ≥ 1`. -/
theorem abs_siftedCount_sub_le (hy : 1 ≤ y)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    |(siftedCount k M z : ℝ) - y * Rk k z| ≤ 2 * y := by
  have h1 := siftedCount_le_add_one hM z
  have h2 : y * Rk k z ≤ y := mul_le_of_le_one_right (by linarith) (Rk_le_one k z)
  have h3 : 0 ≤ y * Rk k z := mul_nonneg (by linarith) (Rk_nonneg k z)
  have h4 : (0 : ℝ) ≤ siftedCount k M z := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- `y^{1/s} ≤ y` for `y ≥ 1`, `s ≥ 1`. -/
theorem rpow_one_div_le_self (hy : 1 ≤ y) {s : ℝ} (hs : 1 ≤ s) : y ^ (1 / s) ≤ y :=
  rpow_le_self_of_one_le hy (by rw [div_le_one (by linarith)]; exact hs)

/-- `pntE z · log z ≤ 2/κ²`. -/
theorem pntE_mul_log_le (hz : 1 ≤ z) : pntE z * log z ≤ 2 / pntκ ^ 2 := by
  have hl := log_nonneg hz
  have hκ := pntκ_pos
  set t := √(log z) with ht
  have ht0 : 0 ≤ t := sqrt_nonneg _
  have hlt : log z = t ^ 2 := (sq_sqrt hl).symm
  have h := pow_div_factorial_le_exp (x := pntκ * t) (by positivity) 2
  simp only [Nat.factorial, Nat.succ_eq_add_one, zero_add, mul_one] at h
  rw [pntE, ← ht, hlt, neg_mul, exp_neg, inv_mul_eq_div, div_le_div_iff₀ (exp_pos _)
    (by positivity)]
  nlinarith [mul_pow pntκ t 2]

/-- `M(s) ≤ 4 𝔐(s)` for `sMin ≤ s`: Lemma 7 for `s ≥ 2`, and `F(3) + 3 - s < 3 = 𝔐(s)` for the
upper sieve with `1 ≤ s ≤ 2`. -/
theorem mainMaj_le_four_mul_bigM (lower : Bool) {s : ℝ} (hs : sMin lower ≤ s) :
    mainMaj lower s ≤ 4 * bigM s := by
  rcases le_or_gt 2 s with h2 | h2
  · exact (mainMaj_lt_four_mul_bigM lower h2).le
  cases lower with
  | true => simp [sMin] at hs; linarith
  | false =>
    simp only [sMin] at hs
    rw [mainMaj_false, FSieve_of_le_three (by linarith), bigM_of_le_two h2.le,
      max_eq_left (by linarith)]
    linarith [FSieve_three_add_lt_four]

/-- Mertens' formula with the PNT error, in the form used in [I71, §5]:
`cR / R(z) ≤ log z (1 + K pntE z)` for `z ≥ 2`. -/
theorem exists_cR_div_R_le {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ≥ 2, cR / R z ≤ log z * (1 + K * pntE z) := by
  obtain ⟨c, hc, hcR⟩ := R_lower
  refine ⟨|CR| / c, by positivity, fun z hz ↦ ?_⟩
  have hl : 0 < log z := log_pos (by linarith)
  have hRz := R_pos z
  have h1 := (abs_le.1 (hR z hz)).1
  have h2 : CR * pntE z ≤ |CR| * pntE z := by
    gcongr; exact pntE_nonneg z; exact le_abs_self CR
  have h3 : 1 / R z ≤ log z / c := by
    rw [div_le_div_iff₀ hRz hc]
    have := hcR z hz
    rw [div_le_iff₀ hl] at this
    linarith
  have hp := pntE_nonneg z
  calc cR / R z ≤ (R z * log z + |CR| * pntE z) / R z := by
        gcongr; linarith
    _ = log z + |CR| * pntE z * (1 / R z) := by field_simp
    _ ≤ log z + |CR| * pntE z * (log z / c) := by gcongr
    _ = log z * (1 + |CR| / c * pntE z) := by ring

end IwaniecLinearSieve
