module

public import IwaniecLinearSieve.Main.Corollary
public import IwaniecLinearSieve.PrimeSums.NthPrime
public import IwaniecLinearSieve.Jacobsthal.ShiftedSieve

@[expose] public section

/-!
# [I71, Theorem 2]: `C₀(r) ≪ r² log² r`

`C₀(r)` is the maximal length of a run of consecutive integers each divisible by one of the
first `r` primes.

Proof ([I71, p. 29]). The interval `M = {x, …, x + N - 1}` satisfies `(*)` with `y = N` and
`k = 1` (`abs_card_filter_dvd_sub_le`). Take `z ≥ P_r + 1` (so that the first `r` primes are
`< z`; [I71] takes `z = P_r`, which misses the prime `P_r` itself), `c = e₁ log log 3 + 1` with
`e₁` from (1.4), and `N = ⌈e^c z²⌉`, so that
`s = log N / log z ∈ [2 + c/log z, 2 + (c + log 2)/log z]`.
By `f(2) = 2` (Lemma 5) we have `1 - f(s)/s ≥ 3 log(s - 1)/s` (we do not use the value
`f(s) = s - 2e^γ log(s - 1)`), and `log(s - 1) ≥ log(1 + c/log z) ≥ 2c/(3 log z)` once
`log z ≥ 2c + 2`, so
`1 - f(s)/s - e₁ log log 3 / log N ≥ (2c - e₁ log log 3)/log N > 0`.
Hence (1.4) gives `A_1(M; z) > 0`: some element of `M` is coprime to the first `r` primes.
So a covered run has length `m < N ≤ e^c z² + 1`, and with `z = max(P_r + 1, e^{2c+2})` and
`P_r ≪ r log r` (`nth_prime_le`) this is `≪ r² log² r`.
-/

open Real Finset Filter

namespace IwaniecLinearSieve

namespace Main

/-- The interval `{x, …, x + N - 1}` satisfies `(*)` with `y = N` (for any `k`). -/
theorem abs_multiplesCount_interval_sub_le (x : ℤ) (N d : ℕ) :
    |(multiplesCount ((range N).val.map fun k : ℕ ↦ x + k) d : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hcount : multiplesCount ((range N).val.map fun k : ℕ ↦ x + k) d =
      #((range N).filter fun k : ℕ ↦ (d : ℤ) ∣ x + k) := by
    rw [multiplesCount, Multiset.countP_map, card_def, filter_val]
  rw [hcount]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, div_zero, sub_zero]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have : #((range N).filter fun k : ℕ ↦ (0 : ℤ) ∣ x + k) ≤ 1 := by
      refine card_le_one.2 fun a ha b hb ↦ ?_
      simp only [mem_filter, zero_dvd_iff] at ha hb
      omega
    exact_mod_cast this
  · exact abs_card_filter_dvd_sub_le x N hd

end Main

open Main

/-- **[I71, Theorem 2]**: `C₀(r) ≪ r² log² r`. If each of `m` consecutive integers
`x, x + 1, …, x + m - 1` is divisible by one of the first `r ≥ 2` primes, then
`m ≤ C r² log² r` for an absolute constant `C`. -/
theorem theorem2 : ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ (x : ℤ) (m : ℕ),
    (∀ k < m, ∃ i < r, (Nat.nth Nat.Prime i : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * r ^ 2 * log r ^ 2 := by
  obtain ⟨e₁, he₁, h14⟩ := corollary_lower
  obtain ⟨Cp, hCp⟩ := nth_prime_le
  have ha := loglog_three_pos
  set c := e₁ * log (log 3) + 1 with hc
  have hc1 : 1 ≤ c := by have := mul_nonneg he₁ ha.le; linarith
  set z₁ := exp (2 * c + 2)
  have hz₁ : 3 ≤ z₁ := by have := add_one_le_exp (2 * c + 2); linarith
  set K := |Cp| + (1 + z₁) / (2 * log 2)
  have hl2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨exp c * K ^ 2 + 1 / (2 * log 2) ^ 2, fun r hr x m hcov => ?_⟩
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlr : log 2 ≤ log r := log_le_log (by norm_num) hr2
  have hrl : 2 * log 2 ≤ r * log r := by nlinarith
  set P : ℝ := ((Nat.nth Nat.Prime (r - 1) : ℕ) : ℝ) with hPdef
  set z := max (P + 1) z₁
  have hz : 2 ≤ z := le_trans (by linarith) (le_max_right _ _)
  have hlz : 2 * c + 2 ≤ log z := by
    rw [le_log_iff_exp_le (by linarith)]; exact le_max_right _ _
  set ℓ := log z
  have hℓ : 0 < ℓ := by linarith
  -- the length `N` and the density `y = N`
  set N := ⌈exp c * z ^ 2⌉₊
  set y : ℝ := (N : ℝ) with hydef
  have hyN1 : exp c * z ^ 2 ≤ y := Nat.le_ceil _
  have hyN2 : y < exp c * z ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hez : 4 ≤ exp c * z ^ 2 := by
    have := one_le_exp (by linarith : (0 : ℝ) ≤ c)
    nlinarith
  have hy1 : 1 < y := by linarith
  -- `m < N`
  have hmN : m < N := by
    by_contra hmN
    rw [not_lt] at hmN
    set M := (range N).val.map fun k : ℕ ↦ x + k
    have hM : ∀ d : ℕ, Squarefree d → d.Coprime 1 → |(multiplesCount M d : ℝ) - y / d| ≤ 1 :=
      fun d _ _ ↦ abs_multiplesCount_interval_sub_le x N d
    have hA : siftedCount 1 M z = 0 := by
      rw [siftedCount, Multiset.countP_eq_zero]
      intro a ha
      obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.1 ha
      obtain ⟨i, hi, hdvd⟩ := hcov k (lt_of_lt_of_le (mem_range.1 hk) hmN)
      push Not
      refine ⟨Nat.nth Nat.Prime i, ?_, hdvd⟩
      rw [primesLTk_one, mem_primesLT]
      refine ⟨Nat.prime_nth_prime i, ?_⟩
      have : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (r - 1) :=
        Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
      have : (Nat.nth Nat.Prime i : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast this
      linarith [le_max_left (P + 1) z₁]
    have h := h14 1 le_rfl M y z hy1 hM hz
    rw [hA, Nat.cast_zero, Nat.cast_one, mul_one, Rk_one] at h
    -- the bracket is nonnegative
    set L := log y
    have hL1 : c + 2 * ℓ ≤ L := by
      have := log_le_log (by positivity) hyN1
      rwa [log_mul (exp_pos c).ne' (by positivity), log_exp, log_pow, Nat.cast_two] at this
    have hL2 : L ≤ log 2 + c + 2 * ℓ := by
      have h2 : y ≤ 2 * (exp c * z ^ 2) := by linarith
      have := log_le_log (by linarith) h2
      rwa [log_mul two_ne_zero (by positivity), log_mul (exp_pos c).ne' (by positivity),
        log_exp, log_pow, Nat.cast_two, ← add_assoc] at this
    have hL0 : 0 < L := by linarith
    set s := L / ℓ with hs
    have hsℓ : s * ℓ = L := by rw [hs]; field_simp
    have hs2 : 2 + c / ℓ ≤ s := by
      rw [hs, le_div_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']; linarith
    have hcℓ : c / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; linarith
    have hcℓ0 : 0 ≤ c / ℓ := by positivity
    have hs4 : s ≤ 4 := by
      rw [hs, div_le_iff₀ hℓ]; linarith [log_two_lt_d9]
    have hs0 : 0 < s := by linarith
    have hf := one_sub_fSieve_div_ge s ⟨by linarith, hs4⟩
    have hlog : 2 * c / (3 * ℓ) ≤ log (s - 1) := by
      have h1 : c / ℓ / (1 + c / ℓ) ≤ log (1 + c / ℓ) := div_one_add_le_log_one_add hcℓ0
      have h2 : log (1 + c / ℓ) ≤ log (s - 1) := log_le_log (by positivity) (by linarith)
      have h3 : 2 * c / (3 * ℓ) ≤ c / ℓ / (1 + c / ℓ) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (ℓ * (1 + c / ℓ)) = ℓ + c := by field_simp
        rw [this]
        nlinarith
      linarith
    have hpos : e₁ * log (log 3) / L ≤ 1 - fSieve s / s := by
      have h3 : 2 * c / L ≤ 3 * log (s - 1) / s := by
        rw [← hsℓ, div_le_div_iff₀ (by positivity) hs0]
        have : 3 * (2 * c / (3 * ℓ)) * (s * ℓ) = 2 * c * s := by field_simp
        nlinarith
      have h4 : e₁ * log (log 3) / L ≤ 2 * c / L :=
        div_le_div_of_nonneg_right (by linarith [mul_nonneg he₁ ha.le]) hL0.le
      linarith
    have hRz := R_pos z
    have : 0 ≤ y * R z * (1 - fSieve s / s - e₁ * log (log 3) / L) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  -- the bound
  have hmN' : (m : ℝ) < exp c * z ^ 2 + 1 :=
    lt_of_lt_of_le (by rw [hydef]; exact_mod_cast hmN) hyN2.le
  have hP := hCp r hr
  have hzK : z ≤ K * (r * log r) := by
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    have h1 : z ≤ P + 1 + z₁ := max_le (by linarith) (by linarith)
    have h2 : Cp * r * log r ≤ |Cp| * (r * log r) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity)
    have h3 : 1 + z₁ ≤ (1 + z₁) / (2 * log 2) * (r * log r) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc z ≤ P + 1 + z₁ := h1
      _ ≤ |Cp| * (r * log r) + (1 + z₁) / (2 * log 2) * (r * log r) := by linarith
      _ = K * (r * log r) := by ring
  have hz0 : 0 ≤ z := by linarith
  have h1 : 1 ≤ (r * log r) ^ 2 / (2 * log 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ (by positivity) hrl 2
  calc (m : ℝ) ≤ exp c * z ^ 2 + 1 := hmN'.le
    _ ≤ exp c * (K * (r * log r)) ^ 2 + (r * log r) ^ 2 / (2 * log 2) ^ 2 := by
        gcongr
    _ = (exp c * K ^ 2 + 1 / (2 * log 2) ^ 2) * r ^ 2 * log r ^ 2 := by ring

end IwaniecLinearSieve
