import IwaniecLinearSieve.Main.Corollary

/-!
# [I71, Theorem 3]

**Theorem 3.** Let `y > 1` and assume `(*)`. Then

* (1.5) `A_k(M; y^{1/s}) = y R_k(y^{1/s}) (1 + O((e/(s log s))^s))` for `s < log y/(log log 3y)⁶`;
* (1.6) `A_k(M; z) = y R_k(z) (1 + O(1/log y))` for
  `log z < log y · log log log 16y / (2 log log 3y)`.

The `O`-constants are absolute (uniform in `k`, `M`, `y`, `s`, `z`).

Proof of (1.5) ([I71, p. 29]). [I71] first replaces `k` by its part `k₁` composed of primes
`≤ z` to bound `log log 3k₁ ≪ log z`; this is unnecessary for us, since Theorem 1
(`theorem1_core`) has no `k` in the error term. For `log log 3y ≥ 1`, `s < log y/(log log 3y)⁶`
implies `s ≤ ξ(y)`, `log y > 2` and `s² log⁶ s ≤ log² y`; so
`δ(s, y) ≤ (1 + 1/log s)^{5s} ≤ exp(5s/log s)`, and by the asymptotics of `𝔐` (`bigM_asymp`)

    δ(s, y) 𝔐(s) ≤ exp(-s log s - s log log s + s - (s/log s)(log log s - C - 5)) ≤ (e/(s log s))^s

for `s ≥ s₁`; for `2 ≤ s ≤ s₁` both sides are bounded above and below. With `f, F ≤ 4𝔐`
(Lemma 7), Theorem 1 gives (1.5) (`exists_delta_mul_bigM_le_rpow`). For `y < e^e`, `s` is bounded
and (1.5) is trivial.

We state (1.5) for `s ≥ 2`; for `s < 2` the expression `(e/(s log s))^s` is not meaningful
(`s log s ≤ 0` for `s ≤ 1`), and Theorem 1 gives no lower bound.

Proof of (1.6). With `s = log y / log z`, the hypothesis is `s > 2 λ / λ₃`, where `λ = log log 3y`
and `λ₃ = log log log 16y ≤ log λ + log 3`. For large `y`:

* if `s < log y/λ⁶`, then `s ≥ λ / log λ` and `s (log s + log log s - 1) ≥ λ`, so
  `(e/(s log s))^s ≤ e^{-λ} ≤ 1/log y` and (1.5) applies ([I71] has a misprint: `2` is missing
  in the proof's range of `log z`);
* if `s ≥ log y/λ⁶`, i.e. `log z ≤ λ⁶` (not covered by [I71]'s proof), the fundamental lemma
  (`fundamental_lemma`) applies.

For bounded `y`, `log z ≪ log y` is bounded and (1.6) is trivial.
-/

open Real Finset Filter

namespace IwaniecLinearSieve

namespace Main

/-- `(e/(s log s))^s = exp(s (1 - log s - log log s))` for `s > 1`. -/
theorem rpow_exp_one_div_eq {s : ℝ} (hs : 1 < s) :
    (exp 1 / (s * log s)) ^ s = exp (s * (1 - log s - log (log s))) := by
  have hl := log_pos hs
  rw [rpow_def_of_pos (by positivity), log_div (exp_pos 1).ne' (by positivity),
    log_mul (by linarith) hl.ne', log_exp]
  ring_nf

/-- `(e/(s log s))^s` is bounded below on `[2, S]`. -/
theorem exists_le_rpow_exp_one_div (S : ℝ) : ∃ e : ℝ, 0 < e ∧ ∀ s : ℝ, 2 ≤ s → s ≤ S →
    e ≤ (exp 1 / (s * log s)) ^ s := by
  set S' := max S 2
  have hS' : 2 ≤ S' := le_max_right _ _
  have hlS' : 0 < log S' := log_pos (by linarith)
  set b₀ := exp 1 / (S' * log S')
  have hb₀ : 0 < b₀ := by positivity
  refine ⟨min 1 (b₀ ^ S'), lt_min one_pos (rpow_pos_of_pos hb₀ _), fun s hs2 hsS => ?_⟩
  have hsS' : s ≤ S' := hsS.trans (le_max_left _ _)
  have hls : 0 < log s := log_pos (by linarith)
  have hbb : b₀ ≤ exp 1 / (s * log s) :=
    div_le_div_of_nonneg_left (exp_pos 1).le (by positivity)
      (mul_le_mul hsS' (log_le_log (by linarith) hsS') hls.le (by linarith))
  rcases le_or_gt 1 (exp 1 / (s * log s)) with h1 | h1
  · exact (min_le_left _ _).trans (one_le_rpow h1 (by linarith))
  · refine (min_le_right _ _).trans ?_
    calc b₀ ^ S' ≤ (exp 1 / (s * log s)) ^ S' := rpow_le_rpow hb₀.le hbb (by linarith)
      _ ≤ (exp 1 / (s * log s)) ^ s :=
          rpow_le_rpow_of_exponent_ge (by positivity) h1.le hsS'

/-- [I71, p. 29]: `δ(s, y) 𝔐(s) ≪ (e/(s log s))^s` for `2 ≤ s < log y/(log log 3y)⁶`
(when `log log 3y ≥ 1`). -/
theorem exists_delta_mul_bigM_le_rpow : ∃ B : ℝ, 0 ≤ B ∧ ∀ y s : ℝ, 1 < y →
    1 ≤ log (log (3 * y)) → 2 ≤ s → s < log y / log (log (3 * y)) ^ 6 →
      delta s y * bigM s ≤ B * (exp 1 / (s * log s)) ^ s := by
  obtain ⟨Ca, s₀, hA⟩ := bigM_asymp
  set s₁ := max (max s₀ 3) (exp (exp (Ca + 5)))
  obtain ⟨e, he, hE⟩ := exists_le_rpow_exp_one_div s₁
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set B := max 1 (3 * exp (5 * s₁ / log 2) / e)
  refine ⟨B, le_max_of_le_left zero_le_one, fun y s hy hlam hs2 hsy => ?_⟩
  set l := log (log (3 * y)) with hl
  have hL : 0 < log y := log_pos hy
  have hs0 : 0 < s := by linarith
  have hls : 0 < log s := log_pos (by linarith)
  have hl6 : 1 ≤ l ^ 6 := one_le_pow₀ hlam
  have hsl : s * l ^ 6 < log y := by rwa [lt_div_iff₀ (by positivity)] at hsy
  have hsL : s < log y := by nlinarith
  have hlogs : log s ≤ l := by
    have h1 : log s ≤ log (log y) := log_le_log hs0 hsL.le
    have h2 : log (log y) ≤ l :=
      log_le_log hL (log_le_log (by linarith) (by linarith))
    linarith
  -- `δ(s, y) ≤ exp(5 s / log s)`
  have hx : s ^ 2 * log s ^ 5 / log y ^ 2 ≤ 1 / log s := by
    rw [div_le_div_iff₀ (by positivity) hls]
    have h1 : log s ^ 6 ≤ l ^ 6 := pow_le_pow_left₀ hls.le hlogs 6
    have h2 : l ^ 6 ≤ l ^ 12 := pow_le_pow_right₀ hlam (by norm_num)
    have h3 : (s * l ^ 6) ^ 2 ≤ log y ^ 2 := pow_le_pow_left₀ (by positivity) hsl.le 2
    calc s ^ 2 * log s ^ 5 * log s = s ^ 2 * log s ^ 6 := by ring
      _ ≤ s ^ 2 * l ^ 12 := by gcongr; linarith
      _ = (s * l ^ 6) ^ 2 := by ring
      _ ≤ 1 * log y ^ 2 := by linarith
  have hδ : delta s y ≤ exp (5 * s / log s) := by
    refine (TheoremFive.one_add_rpow_le_exp (lsx_nonneg (log y) (by linarith))
      (by linarith)).trans (exp_le_exp.2 ?_)
    calc 5 * s * (s ^ 2 * log s ^ 5 / log y ^ 2) ≤ 5 * s * (1 / log s) := by gcongr
      _ = 5 * s / log s := by ring
  have hB0 := bigM_pos s
  have hEs := rpow_exp_one_div_eq (by linarith : (1 : ℝ) < s)
  rcases le_or_gt s₁ s with hs₁ | hs₁
  · -- large `s`: the asymptotics of `𝔐`
    have hss₀ : s₀ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs₁
    have hs3 : 3 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs₁
    have hlls : Ca + 5 ≤ log (log s) := by
      have h1 : exp (exp (Ca + 5)) ≤ s := le_trans (le_max_right _ _) hs₁
      rw [le_log_iff_exp_le (by linarith), le_log_iff_exp_le hs0]; exact h1
    have hlogM := (abs_le.1 (hA s hss₀)).2
    have hM : bigM s = exp (log (bigM s)) := (exp_log hB0).symm
    have hkey : 5 * s / log s + log (bigM s) ≤ s * (1 - log s - log (log s)) := by
      have e1 : s * (log s + log (log s) - 1 + log (log s) / log s) =
          s * (log s + log (log s) - 1) + s / log s * log (log s) := by ring
      have e2 : Ca * s / log s = s / log s * Ca := by ring
      have e3 : 5 * s / log s = s / log s * 5 := by ring
      have hsl0 : 0 < s / log s := by positivity
      have : s / log s * 5 + s / log s * Ca ≤ s / log s * log (log s) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hsl0.le
      linarith
    calc delta s y * bigM s ≤ exp (5 * s / log s) * exp (log (bigM s)) := by
          rw [← hM]; gcongr
      _ = exp (5 * s / log s + log (bigM s)) := (exp_add _ _).symm
      _ ≤ exp (s * (1 - log s - log (log s))) := exp_le_exp.2 hkey
      _ = 1 * (exp 1 / (s * log s)) ^ s := by rw [hEs, one_mul]
      _ ≤ B * (exp 1 / (s * log s)) ^ s := by
          gcongr
          exact le_max_left _ _
  · -- bounded `s`
    have hEe := hE s hs2 hs₁.le
    have h5 : 5 * s / log s ≤ 5 * s₁ / log 2 := by
      gcongr
    calc delta s y * bigM s ≤ exp (5 * s₁ / log 2) * 3 :=
          mul_le_mul (hδ.trans (exp_le_exp.2 h5)) (bigM_le_three s) hB0.le (exp_pos _).le
      _ = 3 * exp (5 * s₁ / log 2) / e * e := by field_simp
      _ ≤ B * (exp 1 / (s * log s)) ^ s := by
          gcongr
          exact le_max_right _ _

end Main

open Main

/-- **[I71, Theorem 3]**, (1.5): under `(*)`, for `2 ≤ s < log y / (log log 3y)⁶`,
`|A_k(M; y^{1/s}) - y R_k(y^{1/s})| ≤ C y R_k(y^{1/s}) (e/(s log s))^s`. -/
theorem theorem3_fst : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (M : Finset ℤ) (y s : ℝ), 1 < y →
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ s →
    s < log y / log (log (3 * y)) ^ 6 →
    |(siftedCount k M (y ^ (1 / s)) : ℝ) - y * Rk k (y ^ (1 / s))| ≤
      C * y * Rk k (y ^ (1 / s)) * (exp 1 / (s * log s)) ^ s := by
  obtain ⟨C₀, hC₀, h1⟩ := theorem1_core
  obtain ⟨B, hB, hδB⟩ := exists_delta_mul_bigM_le_rpow
  have ha := loglog_three_pos
  set Y₁ := exp (exp 1)
  have hY₁ : 1 < Y₁ := by have := add_one_le_exp (exp 1); have := exp_pos 1; linarith
  set S₁ := exp 1 / log (log 3) ^ 6
  obtain ⟨e, he, hE⟩ := exists_le_rpow_exp_one_div S₁
  have hRY := R_pos Y₁
  refine ⟨(2 + C₀) * B + 2 / (R Y₁ * e), by positivity, fun k M y s hy hM hs2 hsy => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hs0 : 0 < s := by linarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  set z := y ^ (1 / s)
  have hT : 0 < y * Rk k z := mul_pos (by linarith) (Rk_pos k z)
  have hE0 : 0 < (exp 1 / (s * log s)) ^ s := by
    have := log_pos (by linarith : (1 : ℝ) < s); positivity
  have hmain : (2 + C₀) * B * (y * Rk k z * (exp 1 / (s * log s)) ^ s) +
      2 / (R Y₁ * e) * (y * Rk k z * (exp 1 / (s * log s)) ^ s) =
      ((2 + C₀) * B + 2 / (R Y₁ * e)) * y * Rk k z * (exp 1 / (s * log s)) ^ s := by ring
  have hp1 : 0 ≤ (2 + C₀) * B * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by positivity
  rcases lt_or_ge y Y₁ with hyY | hyY
  · -- bounded `y`: `s` is bounded and the claim is trivial
    have hl3 : log (log 3) ≤ log (log (3 * y)) :=
      log_le_log (log_pos (by norm_num)) (log_le_log (by norm_num) (by linarith))
    have hsS : s ≤ S₁ := by
      have hLY : log y ≤ exp 1 := by
        rw [← log_exp (exp 1)]; exact log_le_log (by linarith) hyY.le
      calc s ≤ log y / log (log (3 * y)) ^ 6 := hsy.le
        _ ≤ exp 1 / log (log 3) ^ 6 := by gcongr
    have hEe := hE s hs2 hsS
    have hRk : R Y₁ ≤ Rk k z :=
      (R_antitone ((rpow_one_div_le_self hy.le hs1).trans hyY.le)).trans (R_le_Rk k z)
    have h2 : 2 * y ≤ 2 / (R Y₁ * e) * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by
      calc 2 * y = 2 / (R Y₁ * e) * (y * R Y₁ * e) := by field_simp
        _ ≤ 2 / (R Y₁ * e) * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by
            gcongr
    have := abs_siftedCount_sub_le hy.le hM z
    linarith
  -- `log log 3y ≥ 1`
  have hlam := one_le_loglog_of_le hyY
  set l := log (log (3 * y)) with hl
  have hl6 : 1 ≤ l ^ 6 := one_le_pow₀ hlam
  have hsl : s * l ^ 6 < log y := by rwa [lt_div_iff₀ (by positivity)] at hsy
  have hL2 : 2 ≤ log y := by nlinarith
  have hsξ : s ≤ xi y := by
    have h1 : l ^ (11 / 5 : ℝ) ≤ l ^ (6 : ℝ) := rpow_le_rpow_of_exponent_le hlam (by norm_num)
    have h2 : l ^ (6 : ℝ) = l ^ 6 := by exact_mod_cast rpow_natCast l 6
    rw [xi, le_div_iff₀ (by positivity)]
    have h3 : s * l ^ (11 / 5 : ℝ) ≤ s * l ^ 6 := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hs0.le
    linarith
  have hδ := hδB y s hy hlam hs2 hsy
  have hδ1 : 1 ≤ delta s y := TheoremFour.one_le_delta hs1 y
  have hM0 := bigM_pos s
  -- the error terms of Theorem 1 are `≤ (2 + C₀) δ 𝔐`
  have herr : ∀ m : ℝ, 0 ≤ m → m ≤ 4 * bigM s →
      m / s + C₀ * delta s y * bigM s / log y ≤ (2 + C₀) * B * (exp 1 / (s * log s)) ^ s := by
    intro m hm0 hm4
    have e1 : m / s ≤ 2 * (delta s y * bigM s) := by
      have hMd : bigM s ≤ delta s y * bigM s := le_mul_of_one_le_left hM0.le hδ1
      rw [div_le_iff₀ hs0]
      calc m ≤ 4 * (delta s y * bigM s) := by linarith
        _ = 2 * (delta s y * bigM s) * 2 := by ring
        _ ≤ 2 * (delta s y * bigM s) * s := by gcongr
    have e2 : C₀ * delta s y * bigM s / log y ≤ C₀ * (delta s y * bigM s) := by
      rw [div_le_iff₀ hL, mul_assoc]
      have : 0 ≤ C₀ * (delta s y * bigM s) := by positivity
      nlinarith
    calc m / s + C₀ * delta s y * bigM s / log y ≤ (2 + C₀) * (delta s y * bigM s) := by
          linarith
      _ ≤ (2 + C₀) * (B * (exp 1 / (s * log s)) ^ s) := by gcongr
      _ = (2 + C₀) * B * (exp 1 / (s * log s)) ^ s := by ring
  obtain ⟨hup, hlo⟩ := h1 k M y s hy hM hsξ
  have hu := hup hs1
  have hlw := hlo hs2
  have hu' := herr _ (mainMaj_nonneg false s) (mainMaj_le_four_mul_bigM false (by
    simp [sMin]; linarith))
  have hl' := herr _ (fSieve_nonneg s) (by
    simpa using mainMaj_le_four_mul_bigM true (by simpa [sMin] using hs2))
  have hu2 := mul_le_mul_of_nonneg_left hu' hT.le
  have hl2 := mul_le_mul_of_nonneg_left hl' hT.le
  rw [abs_le]
  constructor
  · have q1 : y * Rk k z * (1 - fSieve s / s - C₀ * delta s y * bigM s / log y) =
        y * Rk k z - y * Rk k z * (fSieve s / s + C₀ * delta s y * bigM s / log y) := by ring
    have q2 : y * Rk k z * ((2 + C₀) * B * (exp 1 / (s * log s)) ^ s) =
        (2 + C₀) * B * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by ring
    have h0 : 0 ≤ 2 / (R Y₁ * e) * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by positivity
    linarith
  · have q1 : y * Rk k z * (1 + mainMaj false s / s + C₀ * delta s y * bigM s / log y) =
        y * Rk k z + y * Rk k z * (mainMaj false s / s + C₀ * delta s y * bigM s / log y) := by
      ring
    have q2 : y * Rk k z * ((2 + C₀) * B * (exp 1 / (s * log s)) ^ s) =
        (2 + C₀) * B * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by ring
    have h0 : 0 ≤ 2 / (R Y₁ * e) * (y * Rk k z * (exp 1 / (s * log s)) ^ s) := by positivity
    linarith

namespace Main

/-- `log log 16y ≤ log 3 + log log 3y` (from `16 y ≤ (3y)³`). -/
theorem loglog_sixteen_le {y : ℝ} (hy : 1 < y) :
    log (log (16 * y)) ≤ log 3 + log (log (3 * y)) := by
  have h00 : 1 ≤ y ^ 2 := by nlinarith
  have h0 : y ≤ y ^ 3 := by nlinarith
  have h1 : 16 * y ≤ (3 * y) ^ 3 := by nlinarith
  have h2 : log (16 * y) ≤ 3 * log (3 * y) := by
    have := log_le_log (by linarith) h1
    rwa [log_pow, Nat.cast_ofNat] at this
  have h3 : 0 < log (16 * y) := log_pos (by linarith)
  calc log (log (16 * y)) ≤ log (3 * log (3 * y)) := log_le_log h3 h2
    _ = log 3 + log (log (3 * y)) :=
        log_mul (by norm_num) (log_pos (by linarith : (1 : ℝ) < 3 * y)).ne'

theorem log_three_le_two : log 3 ≤ 2 := by
  rw [log_le_iff_le_exp (by norm_num)]
  linarith [add_one_le_exp (2 : ℝ), add_one_le_exp (1 : ℝ), exp_add 1 1,
    show exp 2 = exp 1 * exp 1 by rw [← exp_add]; norm_num]

/-- `log log log 16y ≤ log log 3y + 1`. -/
theorem logloglog_le {y : ℝ} (hy : 1 < y) :
    log (log (log (16 * y))) ≤ log (log (3 * y)) + 1 := by
  have h16 : 1 < log (16 * y) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    linarith [exp_one_lt_d9]
  have h1 := log_le_sub_one_of_pos (log_pos h16)
  have h2 := loglog_sixteen_le hy
  linarith [log_three_le_two]

/-- `log log log 16y ≤ log 3 + log log log 3y` when `log log 3y ≥ 1`. -/
theorem logloglog_le_log {y : ℝ} (hy : 1 < y) (hl : 1 ≤ log (log (3 * y))) :
    log (log (log (16 * y))) ≤ log 3 + log (log (log (3 * y))) := by
  have h16 : 1 < log (16 * y) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    linarith [exp_one_lt_d9]
  have h2 := loglog_sixteen_le hy
  have h3 : log 3 + log (log (3 * y)) ≤ 3 * log (log (3 * y)) := by
    linarith [log_three_le_two]
  calc log (log (log (16 * y))) ≤ log (3 * log (log (3 * y))) :=
        log_le_log (log_pos h16) (h2.trans h3)
    _ = log 3 + log (log (log (3 * y))) := log_mul (by norm_num) (by linarith)

end Main

open Main

/-- **[I71, Theorem 3]**, (1.6): under `(*)`, for `z ≥ 2` with
`log z < log y · log log log 16y / (2 log log 3y)`,
`|A_k(M; z) - y R_k(z)| ≤ C y R_k(z) / log y`. -/
theorem theorem3_snd : ∃ C : ℝ, ∀ (k : ℕ) (M : Finset ℤ) (y z : ℝ), 1 < y →
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z →
    log z < log y * log (log (log (16 * y))) / (2 * log (log (3 * y))) →
    |(siftedCount k M z : ℝ) - y * Rk k z| ≤ C * y * Rk k z / log y := by
  obtain ⟨C₃, hC₃, h15⟩ := theorem3_fst
  obtain ⟨CF, YF, hCF, hYF, hFL⟩ := fundamental_lemma
  have hev : ∀ᶠ y : ℝ in atTop, YF ≤ y ∧ exp (exp 1) ≤ y ∧
      2 ≤ log (log (log (3 * y))) ∧
      4 + 2 * log (log (log (log (3 * y)))) ≤ log (log (log (3 * y))) := by
    have hm := tendsto_log_atTop.comp tendsto_log_log_three_mul
    filter_upwards [eventually_ge_atTop YF, eventually_ge_atTop (exp (exp 1)),
      hm.eventually (eventually_ge_atTop 2),
      hm.eventually (TheoremFive.eventually_add_mul_log_le 4 2)] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hev
  set Y₂ := max Y₀ 2
  have hY₂ : 1 < Y₂ := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hLY : 0 < log Y₂ := log_pos hY₂
  have ha := loglog_three_pos
  set κ₀ := 1 / 2 + 1 / (2 * log (log 3))
  set Z := log Y₂ * κ₀
  have hRZ := R_pos (exp Z)
  refine ⟨2 * log Y₂ / R (exp Z) + C₃ + CF, fun k M y z hy hM hz hlz => ?_⟩
  have hL : 0 < log y := log_pos hy
  set l := log (log (3 * y)) with hl
  have hl0 : 0 < l := TheoremFour.loglog_three_mul_pos hy
  have hz1 : 1 < z := by linarith
  have hlz0 : 0 < log z := log_pos hz1
  have hT : 0 < y * Rk k z := mul_pos (by linarith) (Rk_pos k z)
  have hTL : 0 ≤ y * Rk k z / log y := by positivity
  have hsplit : (2 * log Y₂ / R (exp Z) + C₃ + CF) * y * Rk k z / log y =
      2 * log Y₂ / R (exp Z) * (y * Rk k z / log y) + C₃ * (y * Rk k z / log y) +
        CF * (y * Rk k z / log y) := by ring
  have hp1 : 0 ≤ 2 * log Y₂ / R (exp Z) * (y * Rk k z / log y) := by positivity
  have hp2 : 0 ≤ C₃ * (y * Rk k z / log y) := by positivity
  have hp3 : 0 ≤ CF * (y * Rk k z / log y) := by positivity
  rw [hsplit]
  rcases lt_or_ge y Y₂ with hyY | hyY
  · -- bounded `y`: `log z ≤ Z` and the claim is trivial
    have hll : log (log 3) ≤ l :=
      log_le_log (log_pos (by norm_num)) (log_le_log (by norm_num) (by linarith))
    have hlll := logloglog_le hy
    have hκ : log (log (log (16 * y))) / (2 * l) ≤ κ₀ := by
      calc log (log (log (16 * y))) / (2 * l) ≤ (l + 1) / (2 * l) := by gcongr
        _ = 1 / 2 + 1 / (2 * l) := by field_simp
        _ ≤ κ₀ := by rw [show κ₀ = 1 / 2 + 1 / (2 * log (log 3)) from rfl]; gcongr
    have hzZ : log z ≤ Z := by
      have hLL : log y ≤ log Y₂ := log_le_log (by linarith) hyY.le
      have hκ0 : 0 ≤ κ₀ := by positivity
      calc log z ≤ log y * log (log (log (16 * y))) / (2 * l) := hlz.le
        _ = log y * (log (log (log (16 * y))) / (2 * l)) := by ring
        _ ≤ log Y₂ * κ₀ := mul_le_mul hLL hκ (by
            have := hlz0.trans hlz
            rw [mul_div_assoc] at this
            exact (pos_of_mul_pos_right this hL.le).le) hLY.le
    have hRk : R (exp Z) ≤ Rk k z := by
      refine (R_antitone ?_).trans (R_le_Rk k z)
      rw [← exp_log (by linarith : (0 : ℝ) < z)]
      exact exp_le_exp.2 hzZ
    have h2 : 2 * y ≤ 2 * log Y₂ / R (exp Z) * (y * Rk k z / log y) := by
      have hLL : log y ≤ log Y₂ := log_le_log (by linarith) hyY.le
      calc 2 * y = 2 * log Y₂ / R (exp Z) * (y * R (exp Z) / log Y₂) := by field_simp
        _ ≤ 2 * log Y₂ / R (exp Z) * (y * Rk k z / log y) := by
            gcongr
    have := abs_siftedCount_sub_le hy.le hM z
    linarith
  obtain ⟨hYF', hee, hm2, hm⟩ := hY₀ y (le_trans (le_max_left _ _) hyY)
  have hlam := one_le_loglog_of_le hee
  set s := log y / log z with hs
  have hs0 : 0 < s := by positivity
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div (by linarith) hz1 hL.ne'
  have hls : log y / s = log z := by rw [hs]; field_simp
  rcases le_or_gt (log y / l ^ 6) s with hsl | hsl
  · -- `log z ≤ λ⁶`: the fundamental lemma
    have hlog : log z ≤ l ^ 6 := by
      rw [← hls, div_le_iff₀ hs0]
      rwa [div_le_iff₀ (by positivity), mul_comm] at hsl
    have := hFL k M y z hYF' hM hz hlog
    rw [show CF * y * Rk k z / log y = CF * (y * Rk k z / log y) by ring] at this
    linarith
  -- `s < log y / λ⁶`: (1.5)
  set m := log l with hm_def
  set l₃ := log (log (log (16 * y))) with hl₃
  have hl₃0 : 0 < l₃ := by
    by_contra h
    push Not at h
    have : log y * l₃ / (2 * l) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hL.le h) (by positivity)
    linarith
  have hl₃m : l₃ ≤ m + 2 := by linarith [logloglog_le_log hy hlam, log_three_le_two]
  have hlm : l = exp m := (exp_log hl0).symm
  have hlogm : log m ≤ m / 2 - 2 := by linarith
  have hm0 : 0 < m := by linarith
  -- `s > 2λ/λ₃ ≥ λ/m`
  have hs1 : 2 * l / l₃ < s := by
    rw [hs, div_lt_div_iff₀ hl₃0 hlz0]
    have := hlz
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hs2 : l / m ≤ 2 * l / l₃ := by
    rw [div_le_div_iff₀ hm0 hl₃0]; nlinarith
  have hlogs : m - log m ≤ log s := by
    have := log_le_log (by positivity) (hs2.trans hs1.le)
    rwa [log_div hl0.ne' hm0.ne'] at this
  have hlogs1 : 1 ≤ log s := by linarith
  have hs2' : 2 ≤ s := by
    have : exp 1 ≤ s := by rw [← exp_log hs0]; exact exp_le_exp.2 hlogs1
    linarith [add_one_le_exp (1 : ℝ)]
  have hE : (exp 1 / (s * log s)) ^ s ≤ 1 / log y := by
    rw [rpow_exp_one_div_eq (by linarith)]
    have hll : 0 ≤ log (log s) := log_nonneg hlogs1
    have h1 : l ≤ 2 * l / l₃ * (m - log m - 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl₃0]; nlinarith
    have h2 : 2 * l / l₃ * (m - log m - 1) ≤ s * (log s - 1) :=
      mul_le_mul hs1.le (by linarith) (by linarith) hs0.le
    have h3 : s * (1 - log s - log (log s)) ≤ -l := by nlinarith
    calc exp (s * (1 - log s - log (log s))) ≤ exp (-l) := exp_le_exp.2 h3
      _ = 1 / log (3 * y) := by
          rw [exp_neg, hl, exp_log (log_pos (by linarith : (1 : ℝ) < 3 * y)), one_div]
      _ ≤ 1 / log y := one_div_le_one_div_of_le hL (log_le_log (by linarith) (by linarith))
  have h := h15 k M y s hy hM hs2' hsl
  rw [hzs] at h
  have : C₃ * y * Rk k z * (exp 1 / (s * log s)) ^ s ≤ C₃ * (y * Rk k z / log y) := by
    rw [show C₃ * y * Rk k z * (exp 1 / (s * log s)) ^ s =
      C₃ * (y * Rk k z) * (exp 1 / (s * log s)) ^ s by ring,
      show C₃ * (y * Rk k z / log y) = C₃ * (y * Rk k z) * (1 / log y) by ring]
    gcongr
  linarith

end IwaniecLinearSieve
