import IwaniecLinearSieve.Jacobsthal.LemmaOne
import IwaniecLinearSieve.Jacobsthal.LemmaTwo
import IwaniecLinearSieve.Jacobsthal.Reduction

/-!
# [I78, Theorem] and [I78, Corollary]

**Theorem** ([I78]). There is an absolute constant `c > 0` such that for any primes
`q₁, …, q_r`, `r > 1`, each interval of length `c (1 - 1/q₁)⁻¹ ⋯ (1 - 1/q_r)⁻¹ r² log r` contains
at least `r²` integers coprime to `q₁ ⋯ q_r` (`iwaniec_theorem`, for `X` consecutive integers
`x, x + 1, …, x + X - 1`).

**Corollary** ([I78]). `C(r) ≪ r² log² r` (`iwaniec_corollary`, derived from the Theorem as in
[I78]; it has the same statement as `iwaniecBound`, which is proved directly from the shifted
sieve).

The proof is [I78, §3]: Lemma 1 (`shiftedSieve_lower`) with `f(d) = d`, `g(n) = n`, `A = B = 1`
and Rosser's weights, Lemma 2 (`lemma2_sum_abs_le`, `lemma2_sum_sigma_ge`) at `y = C z²`, and
`X = ∏ (1 - 1/q)⁻¹ y / log z`, which give `S(𝒜, Q) ≫ y / log² z`. Deviations:

* [I78] takes `z = p_r` and `P = ∏_{p ≤ z} p` (the first `r` primes); with `primesLT`
  (`p < z`) we take `z = p_N + 1`;
* the final step "`y / log² z > r²`" ([I78] `z = p_r`) needs `π(z) ≪ z / log z` (Chebyshev,
  `exists_card_primesLT_le`); the Theorem for small `r`, where `z` is too small for Lemma 2, is
  reduced to the case of `N = N₀ r` primes by adding primes `q > 2N`, which changes
  `∏ (1 - 1/q)⁻¹` by a factor at most `2` and can only decrease the count.
-/

open Finset Real

namespace IwaniecLinearSieve

/-- Chebyshev's bound `π(z) ≤ (log 4 + 1) z / log z` for large `z`. -/
theorem exists_card_primesLT_le :
    ∃ Z : ℝ, ∀ z ≥ Z, (#(primesLT z) : ℝ) ≤ (log 4 + 1) * z / log z := by
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 (Chebyshev.eventually_primeCounting_le one_pos)
  refine ⟨Z, fun z hz ↦ le_trans ?_ (hZ z hz)⟩
  have hsub : primesLT z ⊆ Nat.primesBelow (⌊z⌋₊ + 1) := fun p hp ↦ by
    obtain ⟨hp, hpz⟩ := mem_primesLT.1 hp
    exact Nat.mem_primesBelow.2 ⟨Nat.lt_succ_of_le (Nat.le_floor hpz.le), hp⟩
  have := card_le_card hsub
  rw [Nat.primesBelow_card_eq_primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ] at this
  exact_mod_cast this

/-- `t / 3 ≤ 2 e^γ log (1 + t) / (2 + t)` for `0 ≤ t ≤ 1`. -/
theorem div_three_le_main {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 3 ≤ 2 * exp eulerMascheroniConstant * log (2 + t - 1) / (2 + t) := by
  have hγ : 1 ≤ exp eulerMascheroniConstant :=
    one_le_exp (by linarith [one_half_lt_eulerMascheroniConstant])
  have hlog : t / 2 ≤ log (2 + t - 1) := by
    have h1 := one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 2 + t - 1)
    have h2 : t / 2 ≤ 1 - (2 + t - 1)⁻¹ := by
      rw [show (2 : ℝ) + t - 1 = 1 + t by ring, show 1 - (1 + t)⁻¹ = t / (1 + t) by
        field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hl0 : 0 ≤ log (2 + t - 1) := log_nonneg (by linarith)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- [I78, §3] for `#S = π(z)` primes and `z` large: if `X ≥ K ∏_{q ∈ S} (1 - 1/q)⁻¹ z² / log z`,
then at least `π(z)²` of `x, …, x + X - 1` are coprime to `∏_{q ∈ S} q`. -/
theorem exists_card_coprime_ge_core : ∃ K z₁ : ℝ, 0 ≤ K ∧ ∀ z ≥ z₁, ∀ S : Finset ℕ,
    (∀ q ∈ S, q.Prime) → #S = #(primesLT z) → ∀ (x : ℤ) (X : ℕ),
      K * (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ * (z ^ 2 / log z) ≤ X →
        (#(primesLT z) : ℝ) ^ 2 ≤ #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  obtain ⟨K₅, h5⟩ := lemma2_sum_abs_le
  obtain ⟨C₆, hC₆, h6⟩ := lemma2_sum_sigma_ge
  obtain ⟨Zc, hZc⟩ := exists_card_primesLT_le
  -- `Cy` is the constant `C` of [I78, §3], `y = Cy z²`
  set Cy := exp (3 * (C₆ / 2 + 1))
  have hCy1 : 1 ≤ Cy := one_le_exp (by positivity)
  set K₅' := max K₅ 0
  set K := K₅' * Cy / 4 + 6
  refine ⟨K, max (max Zc (Cy + 1)) 3, by positivity, fun z hz S hS hcard x X hX ↦ ?_⟩
  have hz3 : 3 ≤ z := le_of_max_le_right hz
  have hzC : Cy + 1 ≤ z := (le_max_right _ _).trans (le_of_max_le_left hz)
  have hzZ : Zc ≤ z := (le_max_left _ _).trans (le_of_max_le_left hz)
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  set y := Cy * z ^ 2
  have hz2 : 2 ≤ z := by linarith
  have hzy : z ^ 2 ≤ y := le_mul_of_one_le_left (by positivity) hCy1
  have hyz : y < z ^ 4 := by
    have h1 : Cy < z ^ 2 := by nlinarith
    calc y = Cy * z ^ 2 := rfl
      _ < z ^ 2 * z ^ 2 := mul_lt_mul_of_pos_right h1 (by positivity)
      _ = z ^ 4 := by ring
  have hlCy : log Cy = 3 * (C₆ / 2 + 1) := log_exp _
  have hlCy0 : 0 ≤ log Cy := log_nonneg hCy1
  have hly : log y = log Cy + 2 * log z := by
    rw [log_mul (by positivity) (by positivity), log_pow]
    push_cast
    ring
  have hlCy_le : log Cy ≤ log z := log_le_log (by positivity) (by linarith)
  -- the main term: `∑_{n ∣ P} σ_n / ∏_{p ∣ n} (p - 1) ≥ 1 / log z`
  set t := log Cy / log z
  have ht0 : 0 ≤ t := div_nonneg hlCy0 hlz.le
  have ht1 : t ≤ 1 := (div_le_one hlz).2 hlCy_le
  have hs : log y / log z = 2 + t := by
    simp only [t]
    rw [hly]
    field_simp
    ring
  have hmainσ := h6 y z hz2 hzy hyz
  rw [hs] at hmainσ
  have hm := div_three_le_main ht0 ht1
  have hC6y : C₆ / log y ≤ C₆ / (2 * log z) :=
    div_le_div_of_nonneg_left hC₆ (by positivity) (by rw [hly]; linarith)
  have ht3 : t / 3 = (C₆ / 2 + 1) / log z := by
    simp only [t, hlCy]
    ring
  have hσ : 1 / log z ≤ ∑ B ∈ (primesLT z).powerset,
      (∑ A ∈ B.powerset, rosserWeight y z A) / ∏ p ∈ B, ((p : ℝ) - 1) := by
    have : (C₆ / 2 + 1) / log z - C₆ / (2 * log z) = 1 / log z := by
      field_simp
      ring
    linarith
  -- [I78, Lemma 1] with `f(d) = d`, `g(n) = n`, `A = B = 1`
  obtain ⟨e, he, hle⟩ := exists_bijOn_primesLT_le hS hcard
  have hL1 := shiftedSieve_lower (range X) (fun k : ℕ ↦ x + k) hS he (fun p ↦ (p : ℝ))
    (fun p ↦ (p : ℝ)) (fun p hp ↦ by exact_mod_cast (prime_of_mem_primesLT hp).one_lt)
    (fun p hp ↦ by exact_mod_cast hle p hp) (X := X) (Ac := 1) (Bc := 1) (Nat.cast_nonneg X)
    (fun D hD ↦ by
      simpa [Nat.cast_prod] using
        abs_card_filter_dvd_sub_le x X (prod_pos fun q hq ↦ (hS q (hD hq)).pos))
    (rosserWeight y z) (fun B hB ↦ sum_powerset_rosserWeight_le y hB)
  simp only [one_pow, mul_one, one_mul] at hL1
  -- the remainder, by (5): `∑ |λ_n| ≤ K₅' Cy z² / (4 log² z)`
  have hrem : ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| ≤
      K₅' * Cy * z ^ 2 / (4 * log z ^ 2) := by
    refine (h5 y z hz2 hzy hyz).trans ?_
    have hly2 : 4 * log z ^ 2 ≤ log y ^ 2 := by rw [hly]; nlinarith
    calc K₅ * y / log y ^ 2 ≤ K₅' * y / log y ^ 2 := by
          gcongr
          exact le_max_left _ _
      _ ≤ K₅' * y / (4 * log z ^ 2) := by
          gcongr
      _ = K₅' * Cy * z ^ 2 / (4 * log z ^ 2) := by ring
  -- the main term: `X ∏ (1 - 1/q) ∑ σ_n / ∏ (p - 1) ≥ K z² / log² z`
  set P := ∏ q ∈ S, (1 - (q : ℝ)⁻¹)
  have hP : 0 < P := prod_pos fun q hq ↦ sub_pos.2 (inv_lt_one_of_one_lt₀
    (by exact_mod_cast (hS q hq).one_lt))
  have hXP : K * (z ^ 2 / log z) ≤ X * P := by
    have h := mul_le_mul_of_nonneg_right hX hP.le
    calc K * (z ^ 2 / log z) = K * P⁻¹ * (z ^ 2 / log z) * P := by field_simp
      _ ≤ X * P := h
  have hmain : K * z ^ 2 / log z ^ 2 ≤ X * P * ∑ B ∈ (primesLT z).powerset,
      (∑ A ∈ B.powerset, rosserWeight y z A) / ∏ p ∈ B, ((p : ℝ) - 1) := by
    calc K * z ^ 2 / log z ^ 2 = K * (z ^ 2 / log z) * (1 / log z) := by
          field_simp
      _ ≤ X * P * (1 / log z) := mul_le_mul_of_nonneg_right hXP (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hσ (mul_nonneg (Nat.cast_nonneg X) hP.le)
  -- `π(z)² ≤ 6 z² / log² z`
  have hπ := hZc z hzZ
  have hl4 : log 4 < 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    linarith [log_two_lt_d9]
  have hπ2 : (#(primesLT z) : ℝ) ^ 2 ≤ 6 * z ^ 2 / log z ^ 2 := by
    have h0 : (0 : ℝ) ≤ #(primesLT z) := Nat.cast_nonneg _
    have h1 : (#(primesLT z) : ℝ) ^ 2 ≤ ((log 4 + 1) * z / log z) ^ 2 :=
      pow_le_pow_left₀ h0 hπ 2
    refine h1.trans ?_
    rw [div_pow, mul_pow]
    gcongr
    nlinarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hK : K * z ^ 2 / log z ^ 2 - K₅' * Cy * z ^ 2 / (4 * log z ^ 2) = 6 * z ^ 2 / log z ^ 2 := by
    simp only [K]
    field_simp
    ring
  linarith

/-- Any `r ≤ N` primes extend to `N` primes, all new ones `> b`. -/
theorem exists_superset_card_eq_gt {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hN : #S ≤ N)
    (b : ℕ) : ∃ S' : Finset ℕ, S ⊆ S' ∧ (∀ p ∈ S', p.Prime) ∧ #S' = N ∧ ∀ p ∈ S' \ S, b < p := by
  set U := (range N).image fun i ↦ Nat.nth Nat.Prime (b + i)
  have hU : #U = N := by
    rw [card_image_of_injective _ fun i j h ↦ by
      have := Nat.nth_injective Nat.infinite_setOfPred_prime h
      omega, card_range]
  have : N - #S ≤ #(U \ S) := (Nat.sub_le_sub_right hU.ge _).trans (le_card_sdiff S U)
  obtain ⟨T, hTU, hT⟩ := exists_subset_card_eq this
  have hTU' : ∀ p ∈ T, ∃ i, p = Nat.nth Nat.Prime (b + i) := fun p hp ↦ by
    obtain ⟨i, -, hi⟩ := mem_image.1 (sdiff_subset (hTU hp))
    exact ⟨i, hi.symm⟩
  refine ⟨S ∪ T, subset_union_left, fun p hp ↦ ?_, ?_, fun p hp ↦ ?_⟩
  · rcases mem_union.1 hp with hp | hp
    · exact hS p hp
    · obtain ⟨i, rfl⟩ := hTU' p hp
      exact Nat.prime_nth_prime _
  · rw [card_union_of_disjoint (disjoint_of_subset_right hTU disjoint_sdiff), hT]
    omega
  · obtain ⟨hp, hpS⟩ := mem_sdiff.1 hp
    have hpT : p ∈ T := (mem_union.1 hp).resolve_left hpS
    obtain ⟨i, rfl⟩ := hTU' p hpT
    have := Nat.add_two_le_nth_prime (b + i)
    omega

/-- Adding at most `N` primes `q > 2N` changes `∏ (1 - 1/q)` by a factor at least `1/2`. -/
theorem prod_superset_ge {S S' : Finset ℕ} (hSS' : S ⊆ S') (hS' : ∀ p ∈ S', p.Prime) {N : ℕ}
    (hN : 1 ≤ N) (hcard : #S' ≤ N) (hgt : ∀ p ∈ S' \ S, 2 * N < p) :
    (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) / 2 ≤ ∏ q ∈ S', (1 - (q : ℝ)⁻¹) := by
  rw [← prod_sdiff hSS']
  have hP : 0 ≤ ∏ q ∈ S, (1 - (q : ℝ)⁻¹) := prod_nonneg fun q hq ↦ sub_nonneg.2
    (inv_le_one_of_one_le₀ (by exact_mod_cast (hS' q (hSS' hq)).one_lt.le))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℝ := 1 - 1 / (2 * N)
  have ha0 : 0 ≤ a := by
    simp only [a]
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have ha1 : a ≤ 1 := by simp only [a]; linarith [show 0 < 1 / (2 * (N : ℝ)) by positivity]
  have h1 : a ^ #(S' \ S) ≤ ∏ q ∈ S' \ S, (1 - (q : ℝ)⁻¹) := by
    rw [← prod_const]
    refine prod_le_prod₀ (fun _ _ ↦ ha0) fun q hq ↦ ?_
    have hq : (2 * N : ℝ) < q := by exact_mod_cast hgt q hq
    simp only [a, one_div]
    exact sub_le_sub_left (inv_anti₀ (by positivity) hq.le) 1
  have h2 : a ^ N ≤ a ^ #(S' \ S) :=
    pow_le_pow_of_le_one ha0 ha1 ((card_le_card sdiff_subset).trans hcard)
  have h3 : 1 / 2 ≤ a ^ N := by
    have := one_add_mul_le_pow (a := -(1 / (2 * (N : ℝ)))) (by
      have : 1 / (2 * (N : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith) N
    have e : (1 : ℝ) + N * -(1 / (2 * N)) = 1 / 2 := by field_simp; ring
    rw [e] at this
    simpa [a, sub_eq_add_neg] using this
  calc (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) / 2 = 1 / 2 * ∏ q ∈ S, (1 - (q : ℝ)⁻¹) := by ring
    _ ≤ (∏ q ∈ S' \ S, (1 - (q : ℝ)⁻¹)) * ∏ q ∈ S, (1 - (q : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right (h3.trans (h2.trans h1)) hP

/-- `p_{N₀ r} + 1 ≪_{N₀} r log r`, where `p_n = Nat.nth Nat.Prime (n - 1)` is the `n`-th prime. -/
theorem exists_nth_prime_mul_le (N₀ : ℕ) (hN₀ : 1 ≤ N₀) : ∃ W : ℝ, 0 < W ∧ ∀ r : ℕ, 2 ≤ r →
    (Nat.nth Nat.Prime (N₀ * r - 1) : ℝ) + 1 ≤ W * (r * log r) := by
  obtain ⟨Cp, hCp⟩ := nth_prime_le
  set B : ℝ := N₀ * (log N₀ / log 2 + 1)
  have hN₀' : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hB : 0 ≤ B := by
    have : 0 ≤ log N₀ / log 2 := div_nonneg (log_nonneg hN₀') (log_nonneg (by norm_num))
    positivity
  refine ⟨|Cp| * B + 1, by positivity, fun r hr ↦ ?_⟩
  set N := N₀ * r
  have hN2 : 2 ≤ N := hr.trans (Nat.le_mul_of_pos_left r (by omega))
  have hlog2 : (0.69 : ℝ) < log 2 := by linarith [log_two_gt_d9]
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : log 2 ≤ log r := log_le_log (by norm_num) hr'
  have hrlogr : 1 ≤ (r : ℝ) * log r := by nlinarith
  have hlogN : log N ≤ (log N₀ / log 2 + 1) * log r := by
    rw [Nat.cast_mul, log_mul (by positivity) (by positivity)]
    have : log N₀ ≤ log N₀ / log 2 * log r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hlogr (log_nonneg hN₀')
    linarith
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNlogN0 : 0 ≤ (N : ℝ) * log N := mul_nonneg (by linarith) (log_nonneg (by linarith))
  have hpN : (Nat.nth Nat.Prime (N - 1) : ℝ) ≤ |Cp| * (B * (r * log r)) := by
    have h1 := hCp N hN2
    have h2 : (N : ℝ) * log N ≤ B * (r * log r) := by
      calc (N : ℝ) * log N = N₀ * r * log N := by simp [N]
        _ ≤ N₀ * r * ((log N₀ / log 2 + 1) * log r) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        _ = B * (r * log r) := by ring
    calc (Nat.nth Nat.Prime (N - 1) : ℝ) ≤ Cp * N * log N := h1
      _ = Cp * (N * log N) := by ring
      _ ≤ |Cp| * (N * log N) := mul_le_mul_of_nonneg_right (le_abs_self _) hNlogN0
      _ ≤ |Cp| * (B * (r * log r)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  nlinarith

/-- **[I78, Theorem]**: there is an absolute constant `c > 0` such that for any `r ≥ 2` primes
`S`, any `X ≥ c ∏_{q ∈ S} (1 - 1/q)⁻¹ r² log r` consecutive integers `x, …, x + X - 1` contain at
least `r²` integers coprime to `∏_{q ∈ S} q`. -/
theorem iwaniec_theorem : ∃ c : ℝ, 0 < c ∧ ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → 2 ≤ #S →
    ∀ (x : ℤ) (X : ℕ), c * (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ * ((#S : ℝ) ^ 2 * log #S) ≤ X →
      #S ^ 2 ≤ #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  obtain ⟨K, z₁, hK0, hcore⟩ := exists_card_coprime_ge_core
  set N₀ : ℕ := ⌈z₁⌉₊ + 2
  obtain ⟨W, hW, hWr⟩ := exists_nth_prime_mul_le N₀ (by omega)
  refine ⟨2 * K * W ^ 2 + 1, by positivity, fun S hS hr x X hX ↦ ?_⟩
  set r := #S
  set N := N₀ * r
  have hrN : r ≤ N := Nat.le_mul_of_pos_left r (by omega)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨S', hSS', hS', hcard', hgt⟩ := exists_superset_card_eq_gt hS hrN (2 * N)
  set p := Nat.nth Nat.Prime (N - 1)
  set z : ℝ := p + 1
  have hcardz : #(primesLT z) = N := by
    rw [card_primesLT_nth_prime_add_one]
    omega
  have hz : z₁ ≤ z := by
    have h1 := Nat.add_two_le_nth_prime (N - 1)
    have h2 : N₀ ≤ N := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : z₁ ≤ ⌈z₁⌉₊ := Nat.le_ceil z₁
    have h4 : (⌈z₁⌉₊ : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : ⌈z₁⌉₊ + 1 ≤ p)
    simp only [z]
    linarith
  -- `z ≤ W r log r` and `log r ≤ log z`
  have hzW : z ≤ W * (r * log r) := hWr r hr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlr : 0 < log r := log_pos (by linarith)
  have hrz : (r : ℝ) ≤ z := by
    have h1 := Nat.add_two_le_nth_prime (N - 1)
    have : r ≤ p := by omega
    simp only [z]
    have : (r : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hlrz : log r ≤ log z := log_le_log (by linarith) hrz
  have hz0 : 0 ≤ z := by positivity
  -- the products
  set P := ∏ q ∈ S, (1 - (q : ℝ)⁻¹)
  set P' := ∏ q ∈ S', (1 - (q : ℝ)⁻¹)
  have hP : 0 < P := prod_pos fun q hq ↦ sub_pos.2 (inv_lt_one_of_one_lt₀
    (by exact_mod_cast (hS q hq).one_lt))
  have hPP' : P / 2 ≤ P' := prod_superset_ge hSS' hS' hN1 hcard'.le hgt
  have hP'inv : P'⁻¹ ≤ 2 * P⁻¹ := by
    rw [show 2 * P⁻¹ = (P / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hPP'
  have hzl0 : 0 ≤ z ^ 2 / log z := div_nonneg (sq_nonneg _) (hlr.trans_le hlrz).le
  have hX' : K * P'⁻¹ * (z ^ 2 / log z) ≤ X := by
    have h1 : z ^ 2 / log z ≤ W ^ 2 * (r ^ 2 * log r) := by
      calc z ^ 2 / log z ≤ (W * (r * log r)) ^ 2 / log r :=
            div_le_div₀ (by positivity) (pow_le_pow_left₀ hz0 hzW 2) hlr hlrz
        _ = W ^ 2 * (r ^ 2 * log r) := by field_simp
    calc K * P'⁻¹ * (z ^ 2 / log z) ≤ K * (2 * P⁻¹) * (W ^ 2 * (r ^ 2 * log r)) := by
          gcongr
      _ = 2 * K * W ^ 2 * P⁻¹ * (r ^ 2 * log r) := by ring
      _ ≤ (2 * K * W ^ 2 + 1) * P⁻¹ * (r ^ 2 * log r) := by gcongr; linarith
      _ ≤ X := hX
  have hmz := hcore z hz S' hS' (hcard'.trans hcardz.symm) x X hX'
  rw [hcardz] at hmz
  have hmz' : N ^ 2 ≤ #((range X).filter fun k : ℕ ↦ ∀ q ∈ S', ¬ (q : ℤ) ∣ x + k) := by exact_mod_cast hmz
  have hmono : #((range X).filter fun k : ℕ ↦ ∀ q ∈ S', ¬ (q : ℤ) ∣ x + k) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) :=
    card_le_card fun k hk ↦ by
      simp only [mem_filter] at hk ⊢
      exact ⟨hk.1, fun q hq ↦ hk.2 q (hSS' hq)⟩
  calc r ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hrN 2
    _ ≤ _ := hmz'.trans hmono

/-- **[I78, Corollary]**, derived from the Theorem as in [I78]: if `m` consecutive integers are
each divisible by one of `r ≥ 2` given primes, then `m ≪ (r log r)²`. (The statement is that of
`iwaniecBound`.) -/
theorem iwaniec_corollary : ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
    ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
  obtain ⟨c, hc, hthm⟩ := iwaniec_theorem
  obtain ⟨cR, hcR, hRlow⟩ := R_lower
  obtain ⟨W, hW, hWr⟩ := exists_nth_prime_mul_le 1 le_rfl
  set A := |log W| / log 2 + 2
  refine ⟨c * A / cR, fun S hS hr x m hm ↦ ?_⟩
  set r := #S
  -- the Theorem fails for `X = m`, since no `x + k` is coprime to `∏ S`
  have hzero : #((range m).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk h
    obtain ⟨q, hq, hqk⟩ := hm k (mem_range.1 hk)
    exact h q hq hqk
  have hlt : (m : ℝ) < c * (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ * ((r : ℝ) ^ 2 * log r) := by
    by_contra h
    have := hthm S hS hr x m (not_lt.1 h)
    rw [hzero] at this
    exact (Nat.not_le.2 (pow_pos (by omega : 0 < r) 2)) this
  -- `∏ (1 - 1/q)⁻¹ ≤ 1 / R(p_r + 1) ≤ log (p_r + 1) / cR ≤ A log r / cR`
  set z : ℝ := Nat.nth Nat.Prime (r - 1) + 1
  have hcardz : #(primesLT z) = r := by
    rw [card_primesLT_nth_prime_add_one]
    omega
  have hz2 : 2 ≤ z := by
    have := Nat.add_two_le_nth_prime (r - 1)
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime (r - 1) := by exact_mod_cast (by omega : 2 ≤ _)
    simp only [z]
    linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hRP : R z ≤ ∏ q ∈ S, (1 - (q : ℝ)⁻¹) := R_le_prod_of_card_eq hS hcardz.symm
  have hR0 := R_pos z
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlr : 0 < log r := log_pos (by linarith)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hzW : z ≤ W * (r * log r) := by simpa using hWr r hr
  have hlogz : log z ≤ A * log r := by
    have h1 : log z ≤ log (W * (r * log r)) := log_le_log (by linarith) hzW
    have hlogr_le : log r ≤ r := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h2 : log (W * (r * log r)) ≤ log W + 2 * log r := by
      rw [log_mul hW.ne' (by positivity), log_mul (by positivity) hlr.ne']
      have := log_le_log hlr hlogr_le
      linarith
    have h3 : log W ≤ |log W| / log 2 * log r := by
      have : |log W| ≤ |log W| / log 2 * log r := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left (log_le_log (by norm_num) hr') (abs_nonneg _)
      linarith [le_abs_self (log W)]
    simp only [A]
    linarith
  have hPinv : (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ ≤ A * log r / cR := by
    have h1 : (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ ≤ (R z)⁻¹ := inv_anti₀ hR0 hRP
    have h2 : (R z)⁻¹ ≤ log z / cR := by
      rw [inv_le_comm₀ hR0 (by positivity), inv_div]
      exact hRlow z hz2
    have h3 : log z / cR ≤ A * log r / cR := div_le_div_of_nonneg_right hlogz hcR.le
    linarith
  calc (m : ℝ) ≤ c * (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ * ((r : ℝ) ^ 2 * log r) := hlt.le
    _ ≤ c * (A * log r / cR) * ((r : ℝ) ^ 2 * log r) := by gcongr
    _ = c * A / cR * ((r : ℝ) * log r) ^ 2 := by ring

end IwaniecLinearSieve
