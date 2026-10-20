module

public import IwaniecLinearSieve.Main.Basic

@[expose] public section

/-!
# The fundamental lemma for small `z`

[I71] states the Corollary to Theorem 1 and (1.6) for all `z`, but Theorem 1 only covers
`s = log y / log z ≤ ξ(y)`. For smaller `z` (`log z ≤ λ⁶`, `λ = log log 3y`) we use Rosser's sieve
at the lower level `D = z^{λ + 2}` (the density `y` of `(*)` is unchanged), with the crude bound of
[I71, p. 24] for the deficits and the trivial bound `#D^± ≤ D` for the supports:

* `fail ≤ 2 (e X/λ)^λ = 2 exp(-λ log λ + λ log X + λ)` with `X = 6 log λ + O(1) ≥ Σ_{p<z} 1/p`
  (`fail_le_tail`), and `1/R(z) ≪ log z ≤ λ⁶`, so `fail / R(z) ≤ e^{-λ} ≤ 1/log y`;
* `#D^± ≤ D ≤ exp((λ + 2) λ⁶) ≤ c y / (λ⁶ log y) ≤ y R(z) / log y`, since
  `log y = e^λ - log 3`.

Hence `|A_k(M; z) - y R_k(z)| ≤ 2 y R_k(z) / log y` (`fundamental_lemma`).
-/

open Real Finset Filter

namespace IwaniecLinearSieve

namespace Main

/-- The scalar inequalities in `l = log log 3y` used by the fundamental lemma. -/
theorem eventually_fl (c a : ℝ) (ha : 0 ≤ a) : ∀ᶠ l : ℝ in atTop, 1 ≤ l ∧
    2 * exp 1 * (6 * log l + a + 1) ≤ l ∧
    log (2 / c) + 6 * log l - l * log l + l * log (6 * log l + a + 1) + l ≤ -l ∧
    (l + 2) * l ^ 6 + 6 * log l + l + log 3 - log c ≤ exp l := by
  have hsq : ∀ᶠ l : ℝ in atTop, a + 1 + 12 * log √l ≤ √l :=
    tendsto_sqrt_atTop.eventually (TheoremFive.eventually_add_mul_log_le (a + 1) 12)
  have hpow : ∀ᶠ l : ℝ in atTop, l ^ 8 * exp (-l) ≤ 1 :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).eventually (eventually_le_nhds one_pos)
  filter_upwards [eventually_ge_atTop 1,
    TheoremFive.eventually_add_mul_log_le (2 * exp 1 * (a + 1)) (12 * exp 1),
    TheoremFive.eventually_add_mul_log_le (log (2 / c)) 6, hsq,
    tendsto_log_atTop.eventually (eventually_ge_atTop 8), hpow,
    eventually_ge_atTop (11 + |log 3 - log c|)] with l hl1 hb hc' hs hl8 hp hlB
  have hl0 : 0 < l := by linarith
  have hlog0 : 0 ≤ log l := log_nonneg hl1
  refine ⟨hl1, by linarith, ?_, ?_⟩
  · have hX : 6 * log l + a + 1 ≤ √l := by
      rw [log_sqrt hl0.le] at hs; linarith
    have hlX : log (6 * log l + a + 1) ≤ log l / 2 := by
      rw [← log_sqrt hl0.le]; exact log_le_log (by positivity) hX
    have h1 : l * log (6 * log l + a + 1) ≤ l * (log l / 2) :=
      mul_le_mul_of_nonneg_left hlX hl0.le
    have h2 : 4 * l ≤ l * log l / 2 := by nlinarith
    nlinarith
  · have hle : l ^ 8 ≤ exp l := by
      rw [exp_neg] at hp
      rwa [mul_inv_le_iff₀ (exp_pos l), one_mul] at hp
    have h7 : 1 ≤ l ^ 7 := one_le_pow₀ hl1
    have h67 : l ^ 6 ≤ l ^ 7 := pow_le_pow_right₀ hl1 (by norm_num)
    have h17 : l ≤ l ^ 7 := by
      calc l = l ^ 1 := (pow_one l).symm
        _ ≤ l ^ 7 := pow_le_pow_right₀ hl1 (by norm_num)
    have hlog : log l ≤ l := log_le_self hl0.le
    have hB : log 3 - log c ≤ |log 3 - log c| * l ^ 7 := by
      calc log 3 - log c ≤ |log 3 - log c| := le_abs_self _
        _ ≤ |log 3 - log c| * l ^ 7 := le_mul_of_one_le_right (abs_nonneg _) h7
    have h8 : (11 + |log 3 - log c|) * l ^ 7 ≤ l ^ 8 := by
      rw [show l ^ 8 = l * l ^ 7 by ring]
      exact mul_le_mul_of_nonneg_right hlB (by positivity)
    nlinarith

end Main

open Main

/-- **Fundamental lemma** (for `log z ≤ (log log 3y)⁶`): under `(*)`,
`|A_k(M; z) - y R_k(z)| ≤ C y R_k(z) / log y` for all large `y`, uniformly in `k` and `M`. -/
theorem fundamental_lemma : ∃ C Y : ℝ, 0 ≤ C ∧ 1 < Y ∧ ∀ (k : ℕ) (M : Multiset ℤ) (y z : ℝ),
    Y ≤ y → (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z →
    log z ≤ log (log (3 * y)) ^ 6 →
    |(siftedCount k M z : ℝ) - y * Rk k z| ≤ C * y * Rk k z / log y := by
  obtain ⟨c, hc, hcR⟩ := R_lower
  obtain ⟨C₅, hC₅⟩ := SLT_le_loglog
  set a := |C₅|
  obtain ⟨Y, hY⟩ := eventually_atTop.1 ((tendsto_log_log_three_mul.eventually
    (eventually_fl c a (abs_nonneg _))).and (eventually_ge_atTop 2))
  refine ⟨2, max Y 2, by norm_num, lt_of_lt_of_le one_lt_two (le_max_right _ _),
    fun k M y z hy hM hz hlz => ?_⟩
  obtain ⟨⟨hl1, hb, hE, hD⟩, hy2⟩ := hY y (le_trans (le_max_left _ _) hy)
  set l := log (log (3 * y)) with hl
  have hy1 : 1 < y := by linarith
  have hL : 0 < log y := log_pos hy1
  have hl0 : 0 < l := by linarith
  have hexpl : exp l = log 3 + log y := by
    rw [hl, exp_log (log_pos (by linarith)), log_mul (by norm_num) (by linarith)]
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  have hlog6 : log (l ^ 6) = 6 * log l := by rw [log_pow]; norm_num
  have hz1 : 1 < z := by linarith
  have hlz0 : 0 < log z := log_pos hz1
  set X := 6 * log l + a + 1 with hX
  have hX0 : 0 < X := by have := log_nonneg hl1; positivity
  have hSLT : SLT z ≤ X := by
    have h1 := hC₅ z hz
    have h2 : log (log z) ≤ 6 * log l := by
      rw [← hlog6]; exact log_le_log hlz0 hlz
    have h3 : C₅ ≤ a := le_abs_self C₅
    linarith
  set D := z ^ (l + 2) with hDdef
  have hD1 : 1 < D := one_lt_rpow hz1 (by linarith)
  -- the deficits
  have hfail : ∀ (lower : Bool) (r : ℕ), fail lower r D z / R z ≤ 1 / log y := by
    intro lower r
    have h1 := fail_le_tail (lower := lower) (r := r) hz1 hl0 le_rfl hSLT hb
    rw [exp_one_mul_div_rpow hX0 hl0] at h1
    have h2 : 1 / R z ≤ l ^ 6 / c := by
      have := hcR z hz
      rw [div_le_iff₀ hlz0] at this
      rw [div_le_div_iff₀ (R_pos z) hc]
      nlinarith
    have hl6 : l ^ 6 = exp (6 * log l) := by
      rw [← hlog6, exp_log (by positivity)]
    have h2c : 2 / c = exp (log (2 / c)) := (exp_log (by positivity)).symm
    calc fail lower r D z / R z = fail lower r D z * (1 / R z) := by ring
      _ ≤ 2 * exp (-(l * log l) + l * log X + l) * (l ^ 6 / c) := by
          gcongr
          exact (one_div_pos.2 (R_pos z)).le
      _ = exp (log (2 / c)) * exp (-(l * log l) + l * log X + l) * exp (6 * log l) := by
          rw [← h2c, ← hl6]; ring
      _ = exp (log (2 / c) + 6 * log l - l * log l + l * log X + l) := by
          rw [← exp_add, ← exp_add]; congr 1; ring
      _ ≤ exp (-l) := exp_le_exp.2 hE
      _ = 1 / (log 3 + log y) := by rw [exp_neg, hexpl, one_div]
      _ ≤ 1 / log y := by gcongr; linarith
  -- the supports
  have hcard : ∀ lower : Bool, (#(rosserSet lower D z) : ℝ) ≤ y * R z / log y := by
    intro lower
    have hzD : D ^ (1 / (l + 2)) = z := by
      rw [hDdef, ← rpow_mul (by linarith), mul_one_div_cancel (by linarith), rpow_one]
    have h1 := TheoremFive.card_rosserSet_le (lower := lower) hD1
      (by linarith : (1 : ℝ) ≤ l + 2)
    rw [hzD] at h1
    have hRz : c / l ^ 6 ≤ R z := by
      refine le_trans ?_ (hcR z hz)
      gcongr
    have hDexp : D * l ^ 6 * log y ≤ c * y := by
      have e1 : D = exp ((l + 2) * log z) := by rw [hDdef, rpow_def_of_pos (by linarith), mul_comm]
      have e2 : l ^ 6 = exp (6 * log l) := by rw [← hlog6, exp_log (by positivity)]
      have e3 : log y ≤ exp l := by rw [hexpl]; linarith
      have e4 : c * y = exp (exp l - log 3 + log c) := by
        rw [hexpl, show log 3 + log y - log 3 + log c = log y + log c by ring, exp_add,
          exp_log (by linarith), exp_log hc, mul_comm]
      have e5 : (l + 2) * log z ≤ (l + 2) * l ^ 6 := by gcongr
      calc D * l ^ 6 * log y ≤ exp ((l + 2) * l ^ 6) * exp (6 * log l) * exp l := by
            rw [e1, ← e2]
            gcongr
        _ = exp ((l + 2) * l ^ 6 + 6 * log l + l) := by rw [← exp_add, ← exp_add]
        _ ≤ exp (exp l - log 3 + log c) := exp_le_exp.2 (by linarith)
        _ = c * y := e4.symm
    calc (#(rosserSet lower D z) : ℝ) ≤ D := h1
      _ ≤ c * y / (l ^ 6 * log y) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = y * (c / l ^ 6) / log y := by field_simp
      _ ≤ y * R z / log y := by gcongr
  -- assembly
  set r := #(primesLT z) + 1
  have hr : #(primesLT z) < r := Nat.lt_succ_self _
  have hup := siftedCount_le_fail_of_level (k := k) (D := D) (by linarith) (by linarith) hM hr
  have hlo := fail_le_siftedCount_of_level (k := k) (D := D) (by linarith) (by linarith) hM hr
  have hRk := R_le_Rk k z
  have hyRk : 0 < y * Rk k z := mul_pos (by linarith) (Rk_pos k z)
  have hf1 := mul_le_mul_of_nonneg_left (hfail false r) hyRk.le
  have hf2 := mul_le_mul_of_nonneg_left (hfail true r) hyRk.le
  have hc1 := hcard false
  have hc2 := hcard true
  have hRR : y * R z / log y ≤ y * Rk k z / log y := by gcongr
  have e : y * Rk k z * (1 / log y) = y * Rk k z / log y := by ring
  have e1 : y * Rk k z * (1 + fail false r D z / R z) =
      y * Rk k z + y * Rk k z * (fail false r D z / R z) := by ring
  have e2 : y * Rk k z * (1 - fail true r D z / R z) =
      y * Rk k z - y * Rk k z * (fail true r D z / R z) := by ring
  have e3 : 2 * y * Rk k z / log y = 2 * (y * Rk k z / log y) := by ring
  rw [abs_le, e3]
  constructor <;> linarith

end IwaniecLinearSieve
