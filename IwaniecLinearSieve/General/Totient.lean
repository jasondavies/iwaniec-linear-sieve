module

public import IwaniecLinearSieve.General.Defs
public import IwaniecLinearSieve.PrimeSums.NthPrime
public import IwaniecLinearSieve.Jacobsthal.ShiftedSieve
public import IwaniecLinearSieve.Jacobsthal.Reduction

@[expose] public section

/-!
# `k / φ(k) ≪ log log 3k` ([I71, §5])

* `natCast_div_totient_eq`: `k / φ(k) = (∏_{p ∣ k} (1 - 1/p))⁻¹`.
* `div_totient_le_loglog : ∃ C, ∀ k ≥ 1, k / φ(k) ≤ C log log 3k`: with `r = ω(k)`, the product
  over `p ∣ k` is at least `R(p_r + 1)` (`R_le_prod_of_card_eq`), which is `≫ 1 / log p_r`
  (`R_lower`); `p_r ≪ r log r` (`nth_prime_le`) and `2^r ≤ k`.
* `inv_Rk_le : 1 / R_k(z) ≤ (k / φ(k)) / R(z)`.
-/

open Finset Real

namespace IwaniecLinearSieve

theorem natCast_totient_eq (k : ℕ) :
    (k.totient : ℝ) = k * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors k)
  push_cast at h
  exact h

theorem prod_primeFactors_one_sub_inv_pos (k : ℕ) :
    0 < ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) :=
  prod_pos fun _ hp ↦ one_sub_inv_pos (Nat.prime_of_mem_primeFactors hp)

/-- `k / φ(k) = ∏_{p ∣ k} (1 - 1/p)⁻¹`. -/
theorem natCast_div_totient_eq {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) / k.totient = (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [natCast_totient_eq, div_mul_cancel_left₀ hk0.ne']

theorem one_le_natCast_div_totient {k : ℕ} (hk : 1 ≤ k) : 1 ≤ (k : ℝ) / k.totient := by
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 hk
  rw [one_le_div hφ]
  exact_mod_cast Nat.totient_le k

/-- `2^ω(k) ≤ k`. -/
theorem two_pow_card_primeFactors_le {k : ℕ} (hk : 1 ≤ k) : 2 ^ #k.primeFactors ≤ k := by
  calc 2 ^ #k.primeFactors ≤ ∏ p ∈ k.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ k := Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)

theorem loglog_three_pos : 0 < log (log 3) := log_pos one_lt_log_three

theorem loglog_three_le {k : ℕ} (hk : 1 ≤ k) : log (log 3) ≤ log (log (3 * k)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h3 : (3 : ℝ) ≤ 3 * k := by linarith
  exact log_le_log (log_pos (by norm_num)) (log_le_log (by norm_num) h3)

/-- [I71, §5]: `k / φ(k) ≪ log log 3k`. -/
theorem div_totient_le_loglog :
    ∃ C, ∀ k : ℕ, 1 ≤ k → (k : ℝ) / k.totient ≤ C * log (log (3 * k)) := by
  obtain ⟨c, hc, hR⟩ := R_lower
  obtain ⟨C₁, hC₁⟩ := nth_prime_le
  set C₁' := max C₁ 1
  set l₀ := log (log 3)
  have hl₀ := loglog_three_pos
  -- `log (p_r + 1) ≤ A + 2 log log 3k` for `r = ω(k) ≥ 1`
  set A := max (log 3) (log (2 * C₁') - 2 * log (log 2))
  have hA : 0 ≤ A := (log_nonneg (by norm_num)).trans (le_max_left _ _)
  refine ⟨max (1 / l₀) ((A / l₀ + 2) / c), fun k hk ↦ ?_⟩
  have hL := loglog_three_le hk
  set L := log (log (3 * k))
  have hL0 : 0 < L := hl₀.trans_le hL
  rw [natCast_div_totient_eq hk]
  set r := #k.primeFactors
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · -- `k = 1`
    rw [show k.primeFactors = ∅ from card_eq_zero.1 hr0, prod_empty, inv_one]
    calc (1 : ℝ) = 1 / l₀ * l₀ := by rw [div_mul_cancel₀ _ hl₀.ne']
      _ ≤ max (1 / l₀) ((A / l₀ + 2) / c) * L :=
        mul_le_mul (le_max_left _ _) hL hl₀.le ((div_pos one_pos hl₀).le.trans (le_max_left _ _))
  set z : ℝ := (Nat.nth Nat.Prime (r - 1) : ℝ) + 1
  have hcard : #k.primeFactors = #(primesLT z) := by
    rw [card_primesLT_nth_prime_add_one]
    omega
  have hRz := R_le_prod_of_card_eq (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) hcard
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime (r - 1) := by
    exact_mod_cast (Nat.prime_nth_prime (r - 1)).two_le
  have hz2 : 2 ≤ z := by linarith
  have hlogz : 0 < log z := log_pos (by linarith)
  have hRz' := hR z hz2
  -- `1 / ∏ ≤ 1 / R z ≤ log z / c`
  have h1 : (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ ≤ log z / c := by
    rw [inv_le_comm₀ (prod_primeFactors_one_sub_inv_pos k) (div_pos hlogz hc), inv_div]
    exact hRz'.trans hRz
  -- `log z ≤ A + 2 L`
  have h2 : log z ≤ A + 2 * L := by
    rcases (Nat.succ_le_of_lt hr0).eq_or_lt with hr1 | hr2
    · have : z = 3 := by
        simp only [z, ← hr1, Nat.sub_self, Nat.nth_prime_zero_eq_two]
        norm_num
      rw [this]
      linarith [le_max_left (log 3) (log (2 * C₁') - 2 * log (log 2))]
    · have hr2' : 2 ≤ r := hr2
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2'
      have hlogr : 0 < log r := log_pos (by linarith)
      have hpr := hC₁ r hr2'
      have hlr : log r ≤ r := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hC1' : C₁ ≤ C₁' := le_max_left _ _
      have hC1'' : 1 ≤ C₁' := le_max_right _ _
      -- `z ≤ 2 C₁' r²`
      have hz : z ≤ 2 * C₁' * r ^ 2 := by
        have : C₁ * r * log r ≤ C₁' * r * r := by
          calc C₁ * r * log r ≤ C₁' * r * log r :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1' (by linarith)) hlogr.le
            _ ≤ C₁' * r * r :=
              mul_le_mul_of_nonneg_left hlr (mul_nonneg (by linarith) (by linarith))
        nlinarith
      -- `r ≤ log k / log 2`
      have hk2 : (2 : ℝ) ^ r ≤ k := by exact_mod_cast two_pow_card_primeFactors_le hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hrk : r * log 2 ≤ log k := by
        rw [← log_pow]
        exact log_le_log (pow_pos two_pos r) hk2
      have hlog2 : 0 < log 2 := log_pos one_lt_two
      have hlogk : 0 < log k := lt_of_lt_of_le (mul_pos (by linarith) hlog2) hrk
      have hlr' : log r ≤ log (log k) - log (log 2) := by
        rw [← log_div hlogk.ne' hlog2.ne']
        exact log_le_log (by linarith) ((le_div_iff₀ hlog2).2 hrk)
      have hkk : log (log k) ≤ L :=
        log_le_log hlogk (log_le_log hkpos (by linarith))
      calc log z ≤ log (2 * C₁' * r ^ 2) := log_le_log (by linarith) hz
        _ = log (2 * C₁') + 2 * log r := by
          rw [log_mul (by nlinarith : (0 : ℝ) < 2 * C₁').ne' (pow_pos (by linarith) 2).ne', log_pow]
          push_cast
          ring
        _ ≤ log (2 * C₁') - 2 * log (log 2) + 2 * L := by linarith
        _ ≤ A + 2 * L := by linarith [le_max_right (log 3) (log (2 * C₁') - 2 * log (log 2))]
  calc (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ ≤ log z / c := h1
    _ ≤ (A + 2 * L) / c := by gcongr
    _ ≤ (A / l₀ + 2) / c * L := by
      rw [div_mul_eq_mul_div]
      gcongr
      have : A ≤ A / l₀ * L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl₀]
        exact mul_le_mul_of_nonneg_left hL hA
      linarith
    _ ≤ max (1 / l₀) ((A / l₀ + 2) / c) * L := by gcongr; exact le_max_right _ _

/-- `R(z) ≤ R_k(z)`, hence [I71, §5] `1 / R_k(z) ≤ (k / φ(k)) / R(z)`. -/
theorem inv_Rk_le {k : ℕ} (hk : 1 ≤ k) (z : ℝ) :
    1 / Rk k z ≤ ((k : ℝ) / k.totient) / R z := by
  calc 1 / Rk k z ≤ 1 / R z := one_div_le_one_div_of_le (R_pos z) (R_le_Rk k z)
    _ ≤ ((k : ℝ) / k.totient) / R z :=
      div_le_div_of_nonneg_right (one_le_natCast_div_totient hk) (R_pos z).le

/-- [I71, §5]: `1 / R_k(z) ≤ C log log 3k / R(z)`. -/
theorem inv_Rk_le_loglog : ∃ C, ∀ k : ℕ, 1 ≤ k → ∀ z : ℝ,
    1 / Rk k z ≤ C * log (log (3 * k)) / R z := by
  obtain ⟨C, hC⟩ := div_totient_le_loglog
  exact ⟨C, fun k hk z ↦ (inv_Rk_le hk z).trans
    (div_le_div_of_nonneg_right (hC k hk) (R_pos z).le)⟩

end IwaniecLinearSieve
