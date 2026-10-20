module

public import IwaniecLinearSieve.LinearSieve.TheoremFiveAux
public import IwaniecLinearSieve.LinearSieve.Crude

@[expose] public section

/-!
# Counting lemmas for [I71, Theorem 5]

* `card_rosserSet_le`: `#(rosserSet lower y y^{1/s}) ≤ y` for `y > 1`, `s ≥ 1` (all elements are
  `< y`); this is the small-`y` case.
* `card_filter_succ_le`: Lemma 17 split at a level `w`: the primes `p < w` give at most
  `#(rosserSet lower y w)`.
* `card_rosserSet_rpow_le`: the crude count of `rosserSet lower y w` for `w = y^{1/(ξ-1)}`
  ([I71, p. 27]): elements with at most `K ≈ ξ(1 - 2/λ)` prime factors are counted by
  `π(w)^l / l!`, the others by `card_filter_le_tail`.
* `exists_card_small`: for large `y` and `sMin lower ≤ s ≤ ξ`,
  `1 + #(rosserSet lower y y^{1/(ξ-1)}) ≤ δ(s, y) G(s) y / (8 L⁴)`.
-/

open Real Filter Finset

namespace IwaniecLinearSieve.TheoremFive

variable {lower : Bool} {y z s : ℝ}

/-- For `y > 1` and `s ≥ 1`, every element of `rosserSet lower y y^{1/s}` is `< y`. -/
theorem lt_of_mem_rosserSet_rpow (hy : 1 < y) (hs : 1 ≤ s) {d : ℕ}
    (hd : d ∈ rosserSet lower y (y ^ (1 / s))) : (d : ℝ) < y := by
  by_cases hω : (if lower then 2 else 1) ≤ #d.primeFactors
  · exact lt_of_mem_rosserSet hd hω
  have hsq := squarefree_of_mem_rosserSet hd
  have hz : y ^ (1 / s) ≤ y := by
    conv_rhs => rw [← rpow_one y]
    exact rpow_le_rpow_of_exponent_le hy.le (by rw [div_le_one (by linarith)]; exact hs)
  rcases Nat.lt_or_ge #d.primeFactors 1 with h0 | h1
  · have : d.primeFactors = ∅ := card_eq_zero.1 (by omega)
    rw [Nat.primeFactors_eq_empty] at this
    have hd1 : d = 1 := by have := pos_of_mem_rosserSet hd; omega
    rw [hd1]; simpa using hy
  · -- one prime factor `q < z ≤ y`
    have h1' : #d.primeFactors = 1 := by split_ifs at hω <;> omega
    obtain ⟨q, hq⟩ := card_eq_one.1 h1'
    have hdq : d = q := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hq, prod_singleton]
    have hqz := lt_of_mem_primesLT
      (primeFactors_subset_of_mem_rosserSet hd (by rw [hq]; exact mem_singleton_self q))
    rw [hdq]; linarith

/-- The small-`y` case: `#(rosserSet lower y y^{1/s}) ≤ y` for `y > 1`, `s ≥ 1`. -/
theorem card_rosserSet_le (hy : 1 < y) (hs : 1 ≤ s) :
    (#(rosserSet lower y (y ^ (1 / s))) : ℝ) ≤ y := by
  have hsub : rosserSet lower y (y ^ (1 / s)) ⊆ Ico 1 ⌈y⌉₊ := fun d hd ↦ by
    have := lt_of_mem_rosserSet_rpow hy hs hd
    exact mem_Ico.2 ⟨pos_of_mem_rosserSet hd, Nat.lt_ceil.2 this⟩
  have h := card_le_card hsub
  rw [Nat.card_Ico] at h
  have hc := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ y)
  have : ((⌈y⌉₊ - 1 : ℕ) : ℝ) ≤ y := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (by positivity))]
    push_cast; linarith
  exact (Nat.cast_le.2 h).trans this

/-- Lemma 17 split at `w`: the primes `p < w` contribute (with the `1`) at most
`#(rosserSet lower y w)`. -/
theorem card_filter_succ_le (n : ℕ) (lower : Bool) (y z w : ℝ) :
    (#((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ n + 1) : ℝ) ≤
      #(rosserSet lower y w) + ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p),
        (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) := by
  rw [card_filter_rosserSet_succ, ← sum_filter_add_sum_filter_not (rosserPrimes lower y z)
    (fun p : ℕ ↦ (p : ℝ) < w)]
  push_cast
  have hsub : (rosserPrimes lower y z).filter (fun p : ℕ ↦ (p : ℝ) < w) ⊆
      rosserPrimes lower y w := fun p hp ↦ by
    rw [mem_filter, mem_rosserPrimes, mem_primesLT] at hp
    rw [mem_rosserPrimes, mem_primesLT]
    exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2⟩
  have h1 : (1 : ℝ) + ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ (p : ℝ) < w),
      (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) ≤
      #(rosserSet lower y w) := by
    calc _ ≤ (1 : ℝ) + ∑ p ∈ rosserPrimes lower y w,
          (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) := by
          gcongr
      _ = (#((rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ n + 1) : ℝ) := by
          rw [card_filter_rosserSet_succ, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      _ ≤ #(rosserSet lower y w) := by exact_mod_cast card_filter_le _ _
  have h2 : (rosserPrimes lower y z).filter (fun p : ℕ ↦ ¬ (p : ℝ) < w) =
      (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p) :=
    filter_congr fun p _ ↦ not_lt
  rw [h2]
  linarith

theorem card_primesLT_le {w : ℝ} (hw : 0 ≤ w) : (#(primesLT w) : ℝ) ≤ w + 1 := by
  have h : #(primesLT w) ≤ ⌈w⌉₊ := by
    unfold primesLT Nat.primesBelow
    exact (card_filter_le _ _).trans (card_range _).le
  exact (Nat.cast_le.2 h).trans (Nat.ceil_lt_add_one hw).le

/-- Elements with at most `K` prime factors: at most `(K + 1) (2w)^K` of them (`w ≥ 1`). -/
theorem card_filter_le_le (lower : Bool) (y : ℝ) {w : ℝ} (hw : 1 ≤ w) (K : ℕ) :
    (#((rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ K) : ℝ) ≤
      (K + 1) * (2 * w) ^ K := by
  set D := (rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ K
  have hmaps : Set.MapsTo (fun d ↦ #d.primeFactors) (D : Set ℕ) (range (K + 1)) := by
    intro d hd
    simp only [coe_filter, Set.mem_ofPred_eq, D] at hd
    simpa [Nat.lt_succ_iff] using hd.2
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hπ : (#(primesLT w) : ℝ) ≤ 2 * w := by linarith [card_primesLT_le (by linarith : 0 ≤ w)]
  calc ∑ l ∈ range (K + 1), (#(D.filter fun d ↦ #d.primeFactors = l) : ℝ)
      ≤ ∑ l ∈ range (K + 1), (2 * w) ^ K := by
        refine sum_le_sum fun l hl ↦ ?_
        have hlK : l ≤ K := Nat.lt_succ_iff.1 (mem_range.1 hl)
        have h1 : (#(D.filter fun d ↦ #d.primeFactors = l) : ℝ) ≤
            #((rosserSet lower y w).filter fun d ↦ #d.primeFactors = l) := by
          exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _))
        refine h1.trans ((card_filter_eq_le_pow_div lower y w l).trans ?_)
        have hf : (1 : ℝ) ≤ l.factorial := by exact_mod_cast l.factorial_pos
        calc (#(primesLT w) : ℝ) ^ l / l.factorial ≤ (#(primesLT w) : ℝ) ^ l :=
              div_le_self (by positivity) hf
          _ ≤ (2 * w) ^ l := by gcongr
          _ ≤ (2 * w) ^ K := pow_le_pow_right₀ (by linarith) hlK
    _ = (K + 1) * (2 * w) ^ K := by simp

/-- The crude count of `rosserSet lower y w` for `w = y^{1/(ξ-1)}`, `ξ = xi y`, `λ = lam y`
([I71, p. 27]):
`#(rosserSet lower y w) ≤ e^{L + 2ξ - L/λ} + 2 e^{L - ξ log ξ + ξ log λ + 5ξ}`. -/
theorem card_rosserSet_rpow_le (hy : 1 < y) (hw : 2 ≤ y ^ (1 / (xi y - 1)))
    (hSLT : SLT (y ^ (1 / (xi y - 1))) ≤ 2 * lam y) (hlam : 100 ≤ lam y)
    (h24 : 24 * lam y ≤ xi y) (hlogξ : log (xi y) ≤ lam y) :
    (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      exp (log y + 2 * xi y - log y / lam y) +
        2 * exp (log y - xi y * log (xi y) + xi y * log (lam y) + 5 * xi y) := by
  set L := log y with hL
  set ξ := xi y with hξ
  set m := lam y with hm
  set w := y ^ (1 / (ξ - 1)) with hwdef
  have hL0 : 0 < L := log_pos hy
  have hm0 : 0 < m := by linarith
  have hξ1 : 1 < ξ := by linarith
  set u := ξ * (1 - 2 / m) with hu
  have hv : 1 / 2 ≤ 1 - 2 / m := by
    have : 2 / m ≤ 1 / 2 := by rw [div_le_iff₀ hm0]; linarith
    linarith
  have hv1 : 1 - 2 / m ≤ 1 := by have : 0 ≤ 2 / m := by positivity
                                 linarith
  have hu2 : ξ / 2 ≤ u := by rw [hu]; nlinarith
  have huξ : u ≤ ξ := by rw [hu]; nlinarith
  have hu0 : 0 < u := by linarith
  set K := ⌊u⌋₊ with hK
  have hKu : (K : ℝ) ≤ u := Nat.floor_le hu0.le
  have huK : u < K + 1 := Nat.lt_floor_add_one u
  have hK1 : 1 ≤ K := by
    rw [hK, Nat.one_le_floor_iff]; linarith
  rw [← card_filter_add_card_filter_not (fun d ↦ #d.primeFactors ≤ K)]
  push_cast
  gcongr
  · -- few prime factors
    refine (card_filter_le_le lower y (by linarith) K).trans ?_
    have h2w : 1 ≤ 2 * w := by linarith
    have hA : (K : ℝ) + 1 ≤ exp ξ := by linarith [add_one_le_exp ξ]
    have hB : (2 * w) ^ K ≤ exp ξ * exp (L - L / m) := by
      rw [← rpow_natCast]
      calc (2 * w) ^ (K : ℝ) ≤ (2 * w) ^ u := rpow_le_rpow_of_exponent_le h2w hKu
        _ = 2 ^ u * w ^ u := mul_rpow (by norm_num) (by linarith)
        _ ≤ exp ξ * exp (L - L / m) := by
          gcongr
          · rw [rpow_def_of_pos (by norm_num), exp_le_exp]
            have : log 2 ≤ 1 := by
              linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
            nlinarith
          · rw [hwdef, ← rpow_mul (by linarith), rpow_def_of_pos (by linarith), exp_le_exp,
              ← hL]
            have h1 : 1 / (ξ - 1) * u ≤ 1 - 1 / m := by
              rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith), hu]
              have : ξ / m ≥ 1 - 1 / m := by
                rw [ge_iff_le, le_div_iff₀ hm0]
                have : 1 / m * m = 1 := by field_simp
                nlinarith
              have e1 : ξ * (1 - 2 / m) = ξ - 2 * (ξ / m) := by ring
              have e2 : (1 - 1 / m) * (ξ - 1) = ξ - ξ / m - 1 + 1 / m := by ring
              rw [e1, e2]; linarith
            have := mul_le_mul_of_nonneg_left h1 hL0.le
            calc L * (1 / (ξ - 1) * u) ≤ L * (1 - 1 / m) := this
              _ = L - L / m := by ring
    calc ((K : ℝ) + 1) * (2 * w) ^ K ≤ exp ξ * (exp ξ * exp (L - L / m)) := by
          gcongr
      _ = exp (L + 2 * ξ - L / m) := by rw [← exp_add, ← exp_add]; ring_nf
  · -- many prime factors
    have hfilt : ((rosserSet lower y w).filter fun d ↦ ¬ #d.primeFactors ≤ K) =
        (rosserSet lower y w).filter fun d ↦ K + 1 ≤ #d.primeFactors :=
      filter_congr fun d _ ↦ by omega
    rw [hfilt]
    have hX : 2 * exp 1 * (2 * m) ≤ u := by
      have : exp 1 < 3 := by linarith [exp_one_lt_d9]
      nlinarith
    refine (card_filter_le_tail (by linarith) (by split_ifs <;> omega) hu0
      (by exact_mod_cast huK) hSLT hX).trans ?_
    rw [exp_one_mul_div_rpow (by positivity) hu0]
    have hy' : y = exp L := (exp_log (by linarith)).symm
    rw [hy', mul_assoc, ← exp_add]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)
    -- `u log u ≥ ξ log ξ - 3ξ`
    have hlogv : -1 ≤ log (1 - 2 / m) := by
      have := log_le_log (by norm_num) hv
      have h2 : log (1 / 2) = -log 2 := by rw [one_div, log_inv]
      have : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hlogv0 : log (1 - 2 / m) ≤ 0 := log_nonpos (by linarith) hv1
    have hulog : ξ * log ξ - 3 * ξ ≤ u * log u := by
      rw [hu, log_mul (by linarith) (by linarith)]
      have h1 : (1 - 2 / m) * log (1 - 2 / m) ≥ -1 := by nlinarith
      have h2 : 2 / m * log ξ ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hm0]; linarith
      have hξ0 : 0 ≤ ξ := by linarith
      have e : ξ * (1 - 2 / m) * (log ξ + log (1 - 2 / m)) =
          ξ * log ξ - ξ * (2 / m * log ξ) + ξ * ((1 - 2 / m) * log (1 - 2 / m)) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h2 hξ0, mul_le_mul_of_nonneg_left h1.le hξ0]
    have hlog2m : log (2 * m) ≤ 1 + log m := by
      rw [log_mul (by norm_num) hm0.ne']
      linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogm : 0 ≤ log m := log_nonneg (by linarith)
    have : u * log (2 * m) ≤ ξ * (1 + log m) := by
      have h0 : 0 ≤ log (2 * m) := log_nonneg (by linarith)
      calc u * log (2 * m) ≤ ξ * log (2 * m) := by gcongr
        _ ≤ ξ * (1 + log m) := by gcongr
    nlinarith

/-! ### The comparison (4.9), (4.10) -/

theorem one_le_of_sMin_le (hs : sMin lower ≤ s) : 1 ≤ s := by
  cases lower <;> simp [sMin] at hs <;> linarith

theorem one_le_delta (hs : 1 ≤ s) (y : ℝ) : 1 ≤ delta s y :=
  one_le_rpow (by linarith [lsx_nonneg (log y) hs]) (by linarith)

/-- [I71, (4.9), (4.10)] in the form needed for Theorem 5: for `sMin lower ≤ s ≤ ξ`,
`exp(-ξ log ξ + (3/2) ξ log λ) ≤ δ(s, y) G(s)`, given the lower bound of Lemma 9 with constant
`c_G ≥ 0` and the scalar facts of `eventually_scalar`. For `s ≤ ξ/2` this uses Lemma 9 only; for
`s > ξ/2` it uses `δ(s, y) ≥ (s² log⁵ s / L²)^{5s} ≥ λ^{3s} 128^{-5s}`. -/
theorem exp_le_delta_errMaj {cG : ℝ} (hcG : 0 ≤ cG)
    (hG : ∀ (r : ℕ) (s : ℝ), 3 ≤ s → exp (-(s * log s) - s * log (log s) - cG * s) ≤ majG r s)
    (hy : 1 < y) (h2 : 2 * (cG + 5 * log 128) ≤ log (lam y)) (h6 : 6 ≤ xi y)
    (h8 : lam y / 2 ≤ log (xi y / 2)) (h9 : 4 * log (lam y) + cG ≤ log (xi y))
    (h10 : log (xi y) ≤ lam y) (lower : Bool) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y) :
    exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) ≤ delta s y * errMaj lower s := by
  have hlogξ := log_xi_eq hy
  set L := log y with hL
  set ξ := xi y with hξ
  set m := lam y with hm
  set a := log m with ha
  have hL0 : 0 < L := log_pos hy
  have h128 : 0 ≤ log 128 := log_nonneg (by norm_num)
  have ha0 : 0 ≤ a := by linarith
  have hm0 : 0 < m := lam_pos hy
  have hs1 := one_le_of_sMin_le hs
  have hδ1 := one_le_delta hs1 y
  have hGl : ∀ t ≥ 3, exp (-(t * log t) - t * log (log t) - cG * t) ≤ errMaj lower t := by
    intro t ht; rw [errMaj_eq_majG_succ]; exact hG _ t ht
  have hll : ∀ t, 3 ≤ t → t ≤ ξ → log (log t) ≤ a := fun t ht htξ ↦
    log_le_log (log_pos (by linarith)) ((log_le_log (by linarith) htξ).trans h10)
  rcases le_or_gt s (ξ / 2) with hsh | hsh
  · -- `s ≤ ξ/2`: Lemma 9 at `s' = max s 3`
    set s' := max s 3 with hs'
    have hs'3 : 3 ≤ s' := le_max_right _ _
    have hs'h : s' ≤ ξ / 2 := max_le hsh (by linarith)
    have hGs : errMaj lower s' ≤ errMaj lower s := errMaj_antitone lower (le_max_left _ _)
    have hl0 : 0 ≤ log s' := log_nonneg (by linarith)
    have hl1 : log s' ≤ log ξ := log_le_log (by linarith) (by linarith)
    have hll' := hll s' hs'3 (by linarith)
    have e1 : s' * log s' ≤ ξ / 2 * log ξ := mul_le_mul hs'h hl1 hl0 (by linarith)
    have e2 : s' * log (log s') ≤ ξ / 2 * a :=
      (mul_le_mul_of_nonneg_left hll' (by linarith)).trans
        (mul_le_mul_of_nonneg_right hs'h ha0)
    have e3 : cG * s' ≤ cG * (ξ / 2) := mul_le_mul_of_nonneg_left hs'h hcG
    have e4 : 0 ≤ ξ / 2 * (log ξ - 4 * a - cG) := mul_nonneg (by linarith) (by linarith)
    calc exp (-(ξ * log ξ) + 3 / 2 * ξ * a)
        ≤ exp (-(s' * log s') - s' * log (log s') - cG * s') := exp_le_exp.2 (by nlinarith)
      _ ≤ errMaj lower s' := hGl s' hs'3
      _ ≤ errMaj lower s := hGs
      _ = 1 * errMaj lower s := (one_mul _).symm
      _ ≤ delta s y * errMaj lower s := by
          gcongr; exact (errMaj_pos lower s).le
  · -- `s > ξ/2`: the growth of `δ`
    have hs3 : 3 ≤ s := by linarith
    have hs0 : 0 ≤ s := by linarith
    have hlogs : m / 2 ≤ log s := h8.trans (log_le_log (by linarith) hsh.le)
    set a₀ := ξ ^ 2 * m ^ 5 / (128 * L ^ 2) with ha₀
    have ha₀0 : 0 < a₀ := by have : 0 < ξ := by linarith
                             positivity
    have hx : a₀ ≤ s ^ 2 * log s ^ 5 / L ^ 2 := by
      rw [ha₀, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (ξ / 2) ^ 2 ≤ s ^ 2 := by gcongr
      have h2 : (m / 2) ^ 5 ≤ log s ^ 5 := by gcongr
      have : ξ ^ 2 * m ^ 5 ≤ 128 * (s ^ 2 * log s ^ 5) := by
        have := mul_le_mul h1 h2 (by positivity) (by positivity)
        nlinarith
      nlinarith [sq_nonneg L]
    have hloga₀ : 5 * log a₀ = 3 * a - 5 * log 128 := by
      have hξ0 : 0 < ξ := by linarith
      rw [ha₀, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by norm_num) (by positivity), log_pow, log_pow, log_pow, hlogξ]
      push_cast; ring
    have hδ : exp (s * (3 * a - 5 * log 128)) ≤ delta s y := by
      calc exp (s * (3 * a - 5 * log 128)) = a₀ ^ (5 * s) := by
            rw [rpow_def_of_pos ha₀0, ← hloga₀]; ring_nf
        _ ≤ (1 + s ^ 2 * log s ^ 5 / L ^ 2) ^ (5 * s) :=
            rpow_le_rpow ha₀0.le (by linarith) (by linarith)
        _ = delta s y := rfl
    have hGs : exp (-(s * log s) - s * a - cG * s) ≤ errMaj lower s := by
      refine le_trans (exp_le_exp.2 ?_) (hGl s hs3)
      nlinarith [hll s hs3 hsξ]
    set c₁ := cG + 5 * log 128 with hc₁
    have hqξ : 0 ≤ log ξ - 2 * a + c₁ := by linarith
    have hsq : s * (log s - 2 * a + c₁) ≤ ξ * (log ξ - 2 * a + c₁) := by
      rcases le_or_gt (log s - 2 * a + c₁) 0 with hq | hq
      · nlinarith
      · have : log s ≤ log ξ := log_le_log (by linarith) hsξ
        nlinarith
    have hξc : ξ * (2 * c₁) ≤ ξ * a := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    calc exp (-(ξ * log ξ) + 3 / 2 * ξ * a)
        ≤ exp (s * (3 * a - 5 * log 128) + (-(s * log s) - s * a - cG * s)) :=
          exp_le_exp.2 (by rw [hc₁] at hsq hξc; linarith)
      _ = exp (s * (3 * a - 5 * log 128)) * exp (-(s * log s) - s * a - cG * s) := exp_add _ _
      _ ≤ delta s y * errMaj lower s := by
          gcongr

/-- [I71, p. 27]: for large `y`, `sMin lower ≤ s ≤ ξ` and `w = y^{1/(ξ - 1)}`,
`1 + #(rosserSet lower y w) ≤ δ(s, y) G(s) y / (8 L⁴)`. -/
theorem exists_card_small : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (s : ℝ), sMin lower ≤ s →
    s ≤ xi y → 1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      delta s y * errMaj lower s * y / (8 * log y ^ 4) := by
  obtain ⟨cG₀, hG₀⟩ := majG_ge_exp
  set cG := max cG₀ 0 with hcG
  have hcG0 : 0 ≤ cG := le_max_right _ _
  have hG : ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
      exp (-(s * log s) - s * log (log s) - cG * s) ≤ majG r s := by
    intro r s hs
    refine le_trans (exp_le_exp.2 ?_) (hG₀ r s hs)
    have : cG₀ * s ≤ cG * s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  obtain ⟨C₅, hC₅⟩ := SLT_le_loglog
  obtain ⟨y₁, hy₁⟩ := exists_xi_large
  set c := max 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))) with hc
  have hc1 := le_max_left 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12)))
  have hc2 := le_max_right 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12)))
  have hc3 := le_max_left (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))
  have hc4 := le_max_right (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))
  have hc5 := le_max_left cG (max C₅ 12)
  have hc6 := le_max_right cG (max C₅ 12)
  have hc7 := le_max_left C₅ 12
  have hc8 := le_max_right C₅ 12
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1
    ((eventually_scalar c hc1).and (eventually_ge_atTop y₁))
  refine ⟨y₀, fun y hy lower s hs hsξ ↦ ?_⟩
  obtain ⟨⟨hy3, ha, hμ, hlam, hℓ1, -, h24, h16, h8, h9, h10⟩, hyy₁⟩ := hy₀ y hy
  obtain ⟨hy1, -, -, hw2⟩ := hy₁ y hyy₁
  have hL0 : 0 < log y := log_pos hy1
  have hm0 := lam_pos hy1
  have hξ := xi_pos hy1
  -- `w = y^{1/(ξ-1)}`
  have hξ1 : 0 < xi y - 1 := by linarith
  have hw : 2 ≤ y ^ (1 / (xi y - 1)) :=
    hw2.trans (rpow_one_div_le_rpow_one_div hy1.le hξ1 (by linarith))
  have hwy : y ^ (1 / (xi y - 1)) ≤ y := by
    conv_rhs => rw [← rpow_one y]
    exact rpow_le_rpow_of_exponent_le hy1.le (by rw [div_le_one hξ1]; linarith)
  have hSLT : SLT (y ^ (1 / (xi y - 1))) ≤ 2 * lam y := by
    have h1 := hC₅ _ hw
    have h2 : log (log (y ^ (1 / (xi y - 1)))) ≤ log (log y) :=
      log_le_log (log_pos (by linarith)) (log_le_log (by linarith) hwy)
    linarith
  have hcard := card_rosserSet_rpow_le (lower := lower) hy1 hw hSLT (by linarith) h24 h10
  -- `4 ξ λ² ≤ L`
  have hxl : 4 * (xi y * lam y ^ 2) ≤ log y := by
    have hsplit : lam y ^ (11 / 5 : ℝ) = lam y ^ 2 * lam y ^ (1 / 5 : ℝ) := by
      rw [← rpow_natCast, ← rpow_add hm0]; norm_num
    rw [xi_eq_lam, hsplit]
    have hμ0 : 0 < lam y ^ (1 / 5 : ℝ) := rpow_pos_of_pos hm0 _
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : 4 ≤ lam y ^ (1 / 5 : ℝ) := by linarith
    nlinarith [mul_pos hL0 (pow_pos hm0 2)]
  have hcrude := crude_exponent_le hL0 rfl hℓ1 (by linarith) (a := log (lam y)) (by linarith)
    hxl h24 h16 h10
  have hB := exp_le_delta_errMaj hcG0 hG hy1 (by linarith) (by linarith) h8 (by linarith) h10
    lower hs hsξ
  have hy' : exp (log y - xi y * log (xi y) + 3 / 2 * xi y * log (lam y)) =
      y * exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) := by
    rw [← exp_log (by linarith : 0 < y), ← exp_add, exp_log (by linarith)]; ring_nf
  rw [le_div_iff₀ (by positivity)]
  calc (1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ)) * (8 * log y ^ 4)
      ≤ 8 * log y ^ 4 * (1 + exp (log y + 2 * xi y - log y / lam y) +
          2 * exp (log y - xi y * log (xi y) + xi y * log (lam y) + 5 * xi y)) := by
        nlinarith [pow_pos hL0 4]
    _ ≤ y * exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) := hcrude.trans hy'.le
    _ ≤ y * (delta s y * errMaj lower s) := by gcongr
    _ = delta s y * errMaj lower s * y := by ring

end IwaniecLinearSieve.TheoremFive
