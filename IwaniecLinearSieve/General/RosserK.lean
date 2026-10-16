import IwaniecLinearSieve.General.LemmaOne

/-!
# Rosser's sieve for general `k` ([I71, §2])

Rosser's truncation is `fᵢ(p₁, …, pᵢ) = (y / (p₁ ⋯ pᵢ))^{1/3}` (`rosserTrunc y`, [I71, p. 6]).
For `y ≥ 0` the corresponding supports are the elements of `rosserSet` that are coprime to `k`
and have at most `n` prime factors (`truncSet_rosserTrunc`); for `n ≥ π(z)` the depth condition
is void (`truncSet_rosserTrunc_of_card_le`). Note that our `rosserSet false` also imposes
`p₁ < y^{1/3}` (the case `f [] = y^{1/3}`), which [I71] only does through (2.14).

* `rosserMainK k lower y z = ∑_{d ∈ D^±, (d, k) = 1} μ(d)/d`: the main sums `G_{r,k}`, `D_{r,k}`
  for large `r`, with `rosserMainK 1 = rosserMain`.
* (2.12), (2.13): `rosserMainK_false_le`, `le_rosserMainK_true`; in terms of the deficits
  `fail` of the case `k = 1`: `rosserMainK_false_le_fail`, `le_rosserMainK_true_fail`.
* The Corollary to Lemma 1 for Rosser's weights (`rosser_cor_upper`, `rosser_cor_lower`), and
  combined with (2.12), (2.13) (`siftedCount_le_fail`, `fail_le_siftedCount`): under `(*)`,

      A_k(M; z) ≤ y R_k(z) (1 + fail false r y z / R(z)) + #D⁺(y, z),
      A_k(M; z) ≥ y R_k(z) (1 - fail true r y z / R(z)) - #D⁻(y, z)

  for `r > π(z)`. These are the starting point of [I71, §5].
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace IwaniecLinearSieve

/-- Rosser's truncation functions `fᵢ(p₁, …, pᵢ) = (y / (p₁ ⋯ pᵢ))^{1/3}`. -/
noncomputable def rosserTrunc (y : ℝ) (h : List ℕ) : ℝ := (y / (h.prod : ℝ)) ^ ((1 : ℝ) / 3)

theorem natCast_lt_rpow_one_div_three_iff {Y : ℝ} (hY : 0 ≤ Y) (p : ℕ) :
    (p : ℝ) < Y ^ ((1 : ℝ) / 3) ↔ (p : ℝ) ^ 3 < Y := by
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have h3 : ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  conv_lhs => rw [← Real.pow_rpow_inv_natCast hp (by norm_num : (3 : ℕ) ≠ 0), h3]
  exact Real.rpow_lt_rpow_iff (by positivity) hY (by norm_num)

theorem natCast_lt_rosserTrunc_iff {y : ℝ} (hy : 0 ≤ y) (h : List ℕ) (p : ℕ) :
    (p : ℝ) < rosserTrunc y h ↔ (p : ℝ) ^ 3 < y / h.prod :=
  natCast_lt_rpow_one_div_three_iff (div_nonneg hy (Nat.cast_nonneg _)) p

variable {k : ℕ} {lower : Bool} {y z : ℝ} {d : ℕ}

theorem card_primeFactors_le_card_primesLT (hd : d ∈ rosserSet lower y z) :
    #d.primeFactors ≤ #(primesLT z) :=
  card_le_card (primeFactors_subset_of_mem_rosserSet hd)

/-- Rosser's sieve is the instance `fᵢ = rosserTrunc y` of Lemma 1: for `y ≥ 0`, the depth-`n`
support (after the history `h`) is the set of elements of `rosserSet lower (y / ∏ h) z` coprime
to `k` with at most `n` prime factors. -/
theorem truncSet_rosserTrunc (hy : 0 ≤ y) (k : ℕ) (lower : Bool) (n : ℕ) (h : List ℕ)
    (z : ℝ) : truncSet (rosserTrunc y) k lower n h z =
      (rosserSet lower (y / h.prod) z).filter fun d ↦ d.Coprime k ∧ #d.primeFactors ≤ n := by
  induction n generalizing lower h z with
  | zero =>
    ext d
    simp only [truncSet_zero, mem_singleton, mem_filter, nonpos_iff_eq_zero, card_eq_zero,
      Nat.primeFactors_eq_empty]
    constructor
    · rintro rfl
      exact ⟨one_mem_rosserSet, Nat.coprime_one_left k, Or.inr rfl⟩
    · rintro ⟨hd, -, h0 | h1⟩
      · exact absurd h0 (pos_of_mem_rosserSet hd).ne'
      · exact h1
  | succ n ih =>
    ext d
    rw [mem_truncSet_succ, mem_filter, mem_rosserSet]
    have hprod : ∀ p : ℕ, y / ((h ++ [p]).prod : ℝ) = y / h.prod / p := fun p ↦ by
      rw [List.prod_append, List.prod_singleton, Nat.cast_mul, div_div]
    have hprimes : ∀ p, p ∈ truncPrimes (rosserTrunc y) k lower h z ↔
        p ∈ rosserPrimes lower (y / h.prod) z ∧ ¬ p ∣ k := fun p ↦ by
      rw [mem_truncPrimes, mem_rosserPrimes, mem_primesLTk, natCast_lt_rosserTrunc_iff hy]
      tauto
    simp_rw [ih, mem_filter, hprod, hprimes]
    constructor
    · rintro (rfl | ⟨p, ⟨hp, hpk⟩, e, ⟨he, hek, hen⟩, rfl⟩)
      · exact ⟨Or.inl rfl, Nat.coprime_one_left k, by simp⟩
      have hpp := prime_of_mem_primesLT (rosserPrimes_subset hp)
      refine ⟨Or.inr ⟨p, hp, e, he, rfl⟩,
        Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd hpp).2 hpk, hek⟩, ?_⟩
      rw [card_primeFactors_mul_of_mem_rosserSet hpp he]
      omega
    · rintro ⟨rfl | ⟨p, hp, e, he, rfl⟩, hk, hn⟩
      · exact Or.inl rfl
      have hpp := prime_of_mem_primesLT (rosserPrimes_subset hp)
      obtain ⟨hpk, hek⟩ := Nat.coprime_mul_iff_left.1 hk
      rw [card_primeFactors_mul_of_mem_rosserSet hpp he] at hn
      exact Or.inr ⟨p, ⟨hp, (Nat.Prime.coprime_iff_not_dvd hpp).1 hpk⟩, e,
        ⟨he, hek, by omega⟩, rfl⟩

/-- For `n ≥ π(z)` the depth condition is void: the support of Rosser's sieve for `k` is the set
of elements of `rosserSet` coprime to `k`. -/
theorem truncSet_rosserTrunc_of_card_le (hy : 0 ≤ y) (k : ℕ) (lower : Bool) {n : ℕ}
    (hn : #(primesLT z) ≤ n) :
    truncSet (rosserTrunc y) k lower n [] z = (rosserSet lower y z).filter (·.Coprime k) := by
  rw [truncSet_rosserTrunc hy, List.prod_nil, Nat.cast_one, div_one]
  refine filter_congr fun d hd ↦ ?_
  simp only [and_iff_left_iff_imp]
  exact fun _ ↦ (card_primeFactors_le_card_primesLT hd).trans hn

/-- `∑_{d ∈ D^±, (d, k) = 1} μ(d) / d`: Iwaniec's `G_{r,k}(z)` (`lower = false`) and
`D_{r,k}(z)` (`lower = true`) for Rosser's truncation, at any depth `r` beyond `π(z)`. -/
noncomputable def rosserMainK (k : ℕ) (lower : Bool) (y z : ℝ) : ℝ :=
  ∑ d ∈ (rosserSet lower y z).filter (·.Coprime k), (μ d : ℝ) / d

@[simp] theorem rosserMainK_one (lower : Bool) (y z : ℝ) :
    rosserMainK 1 lower y z = rosserMain lower y z := by
  rw [rosserMainK, rosserMain]
  congr 1
  exact filter_true_of_mem fun d _ ↦ Nat.coprime_one_right d

theorem truncMain_rosserTrunc (hy : 0 ≤ y) (k : ℕ) (lower : Bool) {n : ℕ}
    (hn : #(primesLT z) ≤ n) :
    truncMain (rosserTrunc y) k lower n [] z = rosserMainK k lower y z := by
  rw [truncMain, truncSet_rosserTrunc_of_card_le hy k lower hn, rosserMainK]

/-- [I71, Lemma 2] for Rosser's sieve with `k = 1`: the deficits `truncDef` of the general
framework are our `fail`. -/
theorem truncDef_rosserTrunc_one (hy : 0 ≤ y) {n r : ℕ} (hn : #(primesLT z) ≤ n)
    (hr : #(primesLT z) < r) :
    truncDef (rosserTrunc y) 1 false n [] z = fail false r y z ∧
      truncDef (rosserTrunc y) 1 true n [] z = fail true r y z := by
  have h1 := truncMain_false_eq (f := rosserTrunc y) (k := 1) n [] z
  have h2 := truncMain_true_eq (f := rosserTrunc y) (k := 1) n [] z
  rw [truncMain_rosserTrunc hy 1 _ hn, rosserMainK_one, Rk_one] at h1 h2
  rw [(fail_eq_of_card_lt hr y).1, (fail_eq_of_card_lt hr y).2]
  constructor <;> linarith

/-- The deficits for general `k` are nonnegative: `D_k ≤ R_k(z) ≤ G_k`. -/
theorem Rk_le_rosserMainK_false (hy : 0 ≤ y) (k : ℕ) (z : ℝ) :
    Rk k z ≤ rosserMainK k false y z := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) := by omega
  rw [← truncMain_rosserTrunc hy k false hn, truncMain_false_eq]
  linarith [(truncDef_nonneg (f := rosserTrunc y) (k := k) _).1
    (even_two_mul (#(primesLT z))) [] z]

theorem rosserMainK_true_le_Rk (hy : 0 ≤ y) (k : ℕ) (z : ℝ) :
    rosserMainK k true y z ≤ Rk k z := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) + 1 := by omega
  rw [← truncMain_rosserTrunc hy k true hn, truncMain_true_eq]
  linarith [(truncDef_nonneg (f := rosserTrunc y) (k := k) _).2
    (odd_two_mul_add_one (#(primesLT z))) [] z]

/-- [I71, (2.12)] for Rosser's sieve: `S_{r,k}(z) ≤ (R_k(z)/R(z)) S_{r,1}(z)`. -/
theorem rosserMainK_false_le (hy : 0 ≤ y) (k : ℕ) (z : ℝ) :
    rosserMainK k false y z ≤ Rk k z / R z * rosserMain false y z := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) := by omega
  have := truncMain_false_le (f := rosserTrunc y) (k := k) (even_two_mul (#(primesLT z))) [] z
  rwa [truncMain_rosserTrunc hy k false hn, truncMain_rosserTrunc hy 1 false hn,
    rosserMainK_one] at this

/-- [I71, (2.13)] for Rosser's sieve: `T_{r,k}(z) ≥ (R_k(z)/R(z)) T_{r,1}(z)`. -/
theorem le_rosserMainK_true (hy : 0 ≤ y) (k : ℕ) (z : ℝ) :
    Rk k z / R z * rosserMain true y z ≤ rosserMainK k true y z := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) + 1 := by omega
  have := le_truncMain_true (f := rosserTrunc y) (k := k)
    (odd_two_mul_add_one (#(primesLT z))) [] z
  rwa [truncMain_rosserTrunc hy k true hn, truncMain_rosserTrunc hy 1 true hn,
    rosserMainK_one] at this

/-- (2.12) with Lemma 2 for `k = 1`: `G_k(z) ≤ R_k(z) (1 + fail false r y z / R(z))`. -/
theorem rosserMainK_false_le_fail (hy : 0 ≤ y) (k : ℕ) {r : ℕ} (hr : #(primesLT z) < r) :
    rosserMainK k false y z ≤ Rk k z * (1 + fail false r y z / R z) := by
  refine (rosserMainK_false_le hy k z).trans_eq ?_
  rw [rosserMain_false_eq hr]
  field_simp [(R_pos z).ne']

/-- (2.13) with Lemma 2 for `k = 1`: `D_k(z) ≥ R_k(z) (1 - fail true r y z / R(z))`. -/
theorem le_rosserMainK_true_fail (hy : 0 ≤ y) (k : ℕ) {r : ℕ} (hr : #(primesLT z) < r) :
    Rk k z * (1 - fail true r y z / R z) ≤ rosserMainK k true y z := by
  refine le_of_eq_of_le ?_ (le_rosserMainK_true hy k z)
  rw [rosserMain_true_eq hr]
  field_simp [(R_pos z).ne']

variable {M : Multiset ℤ}

/-- [I71, (2.7)] for Rosser's sieve: under `(*)`, `A_k(M; z) ≤ y G_k(z) + Σ₁(z)`, where
`Σ₁(z) = #{d ∈ D⁺ : (d, k) = 1}`. -/
theorem rosser_cor_upper (hy : 0 ≤ y)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    (siftedCount k M z : ℝ) ≤
      y * rosserMainK k false y z + #((rosserSet false y z).filter (·.Coprime k)) := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) := by omega
  have := lemma1_cor_upper (f := rosserTrunc y) (even_two_mul (#(primesLT z))) [] hM z
  rwa [truncMain_rosserTrunc hy k false hn, truncSet_rosserTrunc_of_card_le hy k false hn] at this

/-- [I71, (2.8)] for Rosser's sieve: under `(*)`, `A_k(M; z) ≥ y D_k(z) - Σ₂(z)`, where
`Σ₂(z) = #{d ∈ D⁻ : (d, k) = 1}`. -/
theorem rosser_cor_lower (hy : 0 ≤ y)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    y * rosserMainK k true y z - #((rosserSet true y z).filter (·.Coprime k)) ≤
      (siftedCount k M z : ℝ) := by
  have hn : #(primesLT z) ≤ 2 * #(primesLT z) + 1 := by omega
  have := lemma1_cor_lower (f := rosserTrunc y) (odd_two_mul_add_one (#(primesLT z))) [] hM z
  rwa [truncMain_rosserTrunc hy k true hn, truncSet_rosserTrunc_of_card_le hy k true hn] at this

/-- (2.7), Lemma 2 and (2.12) combined: under `(*)`, for `r > π(z)`,
`A_k(M; z) ≤ y R_k(z) (1 + fail false r y z / R(z)) + #D⁺(y, z)`. -/
theorem siftedCount_le_fail (hy : 0 ≤ y)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) {r : ℕ}
    (hr : #(primesLT z) < r) :
    (siftedCount k M z : ℝ) ≤
      y * Rk k z * (1 + fail false r y z / R z) + #(rosserSet false y z) := by
  have h1 := rosser_cor_upper hy hM z
  have h2 := mul_le_mul_of_nonneg_left (rosserMainK_false_le_fail hy k hr) hy
  have h3 : (#((rosserSet false y z).filter (·.Coprime k)) : ℝ) ≤ #(rosserSet false y z) := by
    exact_mod_cast card_filter_le _ _
  rw [← mul_assoc] at h2
  linarith

/-- (2.8), Lemma 2 and (2.13) combined: under `(*)`, for `r > π(z)`,
`A_k(M; z) ≥ y R_k(z) (1 - fail true r y z / R(z)) - #D⁻(y, z)`. -/
theorem fail_le_siftedCount (hy : 0 ≤ y)
    (hM : ∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) {r : ℕ}
    (hr : #(primesLT z) < r) :
    y * Rk k z * (1 - fail true r y z / R z) - #(rosserSet true y z) ≤
      (siftedCount k M z : ℝ) := by
  have h1 := rosser_cor_lower hy hM z
  have h2 := mul_le_mul_of_nonneg_left (le_rosserMainK_true_fail hy k hr) hy
  have h3 : (#((rosserSet true y z).filter (·.Coprime k)) : ℝ) ≤ #(rosserSet true y z) := by
    exact_mod_cast card_filter_le _ _
  rw [← mul_assoc] at h2
  linarith

end IwaniecLinearSieve
