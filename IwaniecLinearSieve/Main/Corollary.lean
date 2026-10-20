module

public import IwaniecLinearSieve.Main.TheoremOne
public import IwaniecLinearSieve.Main.Fundamental

@[expose] public section

/-!
# The Corollary to [I71, Theorem 1]

**Corollary** ((1.3), (1.4)). Let `y > 1`, assume `(*)`, and put `s = log y / log z`. Then

* (1.3) `A_k(M; z) < y R_k(z) (1 + F(s)/s + e₁ log log 3k / log y)`;
* (1.4) `A_k(M; z) > y R_k(z) (1 - f(s)/s - e₁ log log 3k / log y)`.

[I71] gives no range for `z`. Our ranges and conventions:

* (1.4) holds for all `z ≥ 2`. For `s < 2` it is trivial: `f(s) = f(2) = 2` there, so the
  bracket is negative.
* (1.3) holds for `2 ≤ z ≤ y` (`s ≥ 1`), with `F(s) + (3 - s)⁺` in place of `F(s)`. The two agree
  for `s ≥ 3`. Below 3 our `FSieve` is constant (`F(s) = F(3)`, [I71, (3.7)]), and with it the bound
  would claim `1 + F(3)/s` where the Jurkat–Richert upper bound is `2e^γ/s = 1 + (F(3) + 3 - s)/s`.
  For `z > y` (`s < 1`) the error term `e₁ log log 3k / log y` is not relative to the main term
  `≍ 1/s`, so the statement in this form cannot follow from the case `z = y` (and the sieve
  level `y` is then below `z`).

Proof. Constants: `C` from Theorem 1 (`theorem1_core`), `B ≥ δ(s, y) 𝔐(s)` on `1 ≤ s ≤ ξ(y)`
(`exists_delta_mul_bigM_le`), `C_F`, `Y_F` from the fundamental lemma, and
`Y = max Y_F e^e` (so `log log 3y ≥ 1` for `y ≥ Y`).

* `y < Y`: `A ≤ y + 1 < 2y`, while the error term alone is `≥ 2y` once `e₁` is large, because
  `R_k(z) ≥ R(Y)` and `log y ≤ log Y`; for (1.4) the bracket is negative.
* `y ≥ Y`, `s ≤ ξ(y)`: Theorem 1 with `δ 𝔐 ≤ B`.
* `y ≥ Y`, `s > ξ(y)`: then `log z < log y / ξ(y) = (log log 3y)^{11/5} ≤ (log log 3y)⁶`, and the
  fundamental lemma gives `|A - y R_k(z)| ≤ C_F y R_k(z) / log y`.

The bound `δ(s, y) 𝔐(s) ≤ B` for `1 ≤ s ≤ ξ(y)` (`exists_delta_mul_bigM_le`): for large `y`,
`s² log⁴ s / L² ≤ ξ² log⁴ ξ / L² ≤ (log log 3y)^{-2/5} ≤ 1/10`, so
`δ ≤ exp(5 s · s² log⁵ s / L²) ≤ exp(s log s / 2)`, while Lemma 9 gives
`𝔐(s) ≤ 3 exp(-s log s - s log log s + c₂ s)`; and `s (c₂ - log s / 2)` is bounded above.
For bounded `y`, `s` and `s / log y ≤ (log log 3)^{-11/5}` are bounded.
-/

open Real Finset Filter

namespace IwaniecLinearSieve

namespace Main

/-- `s (c - log s / 2) ≤ |c| e^{2|c|}` for `s ≥ 1`. -/
theorem mul_sub_log_div_two_le (c : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    s * (c - log s / 2) ≤ |c| * exp (2 * |c|) := by
  have hl := log_nonneg hs
  have hc := le_abs_self c
  rcases le_or_gt (2 * |c|) (log s) with h | h
  · have : s * (c - log s / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact this.trans (by positivity)
  · have hs' : s < exp (2 * |c|) := by
      rw [← exp_log (by linarith : 0 < s)]; exact exp_lt_exp.2 h
    calc s * (c - log s / 2) ≤ s * |c| := by gcongr; linarith
      _ ≤ exp (2 * |c|) * |c| := by gcongr
      _ = |c| * exp (2 * |c|) := by ring

/-- `δ(s, y) 𝔐(s)` is bounded on `1 ≤ s ≤ ξ(y)`. -/
theorem exists_delta_mul_bigM_le : ∃ B : ℝ, 0 ≤ B ∧
    ∀ y s : ℝ, 1 < y → 1 ≤ s → s ≤ xi y → delta s y * bigM s ≤ B := by
  obtain ⟨c₂, hc₂⟩ := majG_mul_exp_le
  have hev : ∀ᶠ y : ℝ in atTop, 1 ≤ log (log (3 * y)) ∧
      log (log (3 * y)) ^ (-(2 / 5 : ℝ)) ≤ 1 / 10 ∧ 3 ≤ xi y ∧ 1 ≤ log y :=
    (tendsto_log_log_three_mul.eventually (eventually_ge_atTop 1)).and
      ((((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
        tendsto_log_log_three_mul).eventually (eventually_le_nhds (by norm_num))).and
      ((tendsto_xi.eventually (eventually_ge_atTop 3)).and
        (tendsto_log_atTop.eventually (eventually_ge_atTop 1))))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hev
  set Y := max Y₀ 2
  have ha := loglog_three_pos
  set A₁ := 1 / log (log 3) ^ (11 / 5 : ℝ)
  set Ξ := log Y / log (log 3) ^ (11 / 5 : ℝ)
  set B₁ := 3 * exp (|c₂| * exp (2 * |c₂|))
  set B₂ := 3 * (1 + 9 * log 3 ^ 5) ^ (15 : ℝ)
  set B₃ := 3 * (1 + A₁ ^ 2 * log Ξ ^ 5) ^ (5 * Ξ)
  refine ⟨max B₁ (max B₂ B₃), le_max_of_le_left (by positivity), fun y s hy hs1 hsξ => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hB3 := bigM_le_three s
  have hB0 := (bigM_pos s).le
  have hδ0 : 0 ≤ delta s y := (delta_pos hs1 y).le
  rcases lt_or_ge y Y with hyY | hyY
  · -- bounded `y`
    refine le_max_of_le_right (le_max_of_le_right ?_)
    have hsΞ : s ≤ Ξ := hsξ.trans (TheoremFive.xi_le_of_lt hy hyY)
    have hl3 : log 3 ≤ log (3 * y) := log_le_log (by norm_num) (by linarith)
    have hll3 : log (log 3) ≤ log (log (3 * y)) :=
      log_le_log (log_pos (by norm_num)) hl3
    have hlam : log (log 3) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) :=
      rpow_le_rpow ha.le hll3 (by norm_num)
    have hsL : s / log y ≤ A₁ := by
      have hξ : xi y ≤ log y * A₁ := by
        rw [xi, mul_one_div]
        exact div_le_div_of_nonneg_left hL.le (rpow_pos_of_pos ha _) hlam
      rw [div_le_iff₀ hL]; linarith
    have hls : 0 ≤ log s := log_nonneg hs1
    have hlΞ : log s ≤ log Ξ := log_le_log (by linarith) hsΞ
    have hbase : 1 + s ^ 2 * log s ^ 5 / log y ^ 2 ≤ 1 + A₁ ^ 2 * log Ξ ^ 5 := by
      have : s ^ 2 * log s ^ 5 / log y ^ 2 = (s / log y) ^ 2 * log s ^ 5 := by
        field_simp
      rw [this]
      gcongr
    have h1 : (1 : ℝ) ≤ 1 + A₁ ^ 2 * log Ξ ^ 5 := by
      have : 0 ≤ log Ξ := hls.trans hlΞ
      have : 0 ≤ A₁ := by positivity
      nlinarith [pow_nonneg ‹0 ≤ log Ξ› 5, sq_nonneg A₁]
    have hδ : delta s y ≤ (1 + A₁ ^ 2 * log Ξ ^ 5) ^ (5 * Ξ) := by
      calc delta s y ≤ (1 + A₁ ^ 2 * log Ξ ^ 5) ^ (5 * s) :=
            rpow_le_rpow (by linarith [lsx_nonneg (log y) hs1]) hbase (by linarith)
        _ ≤ (1 + A₁ ^ 2 * log Ξ ^ 5) ^ (5 * Ξ) :=
            rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc delta s y * bigM s ≤ (1 + A₁ ^ 2 * log Ξ ^ 5) ^ (5 * Ξ) * 3 :=
          mul_le_mul hδ hB3 hB0 (rpow_nonneg (by linarith) _)
      _ = B₃ := by ring
  obtain ⟨hlam1, hlam, hξ3, hL1⟩ := hY₀ y (le_trans (le_max_left _ _) hyY)
  rcases lt_or_ge s 3 with hs3 | hs3
  · refine le_max_of_le_right (le_max_of_le_left ?_)
    calc delta s y * bigM s ≤ (1 + 9 * log 3 ^ 5) ^ (15 : ℝ) * 3 :=
          mul_le_mul (delta_le_of_le_three hs1 hs3.le hL1) hB3 hB0 (by positivity)
      _ = B₂ := by ring
  refine le_max_of_le_left ?_
  have hs0 : 0 < s := by linarith
  have hls : 1 ≤ log s := by
    have := one_lt_log_three; linarith [log_le_log (by norm_num) hs3]
  -- `𝔐(s) ≤ 3 exp(c₂ s - s log s - s log log s)` (Lemma 9)
  have hM : bigM s ≤ 3 * exp (c₂ * s - (s * log s + s * log (log s))) := by
    have h1 := hc₂ 0 s hs3
    have h2 := (majG_mem 0 s).1
    rw [exp_sub]
    rw [← le_div_iff₀ (exp_pos _)] at h1
    linarith
  -- `δ(s, y) ≤ exp(s log s / 2)`
  have hw : s ^ 2 * log s ^ 4 / log y ^ 2 ≤ 1 / 10 := by
    have h1 := xi_sq_mul_log_pow_four_div_le hy hlam1 (by linarith)
    have h2 : s ^ 2 * log s ^ 4 ≤ xi y ^ 2 * log (xi y) ^ 4 := by
      gcongr
    calc s ^ 2 * log s ^ 4 / log y ^ 2 ≤ xi y ^ 2 * log (xi y) ^ 4 / log y ^ 2 := by gcongr
      _ ≤ 1 / 10 := h1.trans hlam
  have hδ : delta s y ≤ exp (s * log s / 2) := by
    refine (TheoremFive.one_add_rpow_le_exp (lsx_nonneg (log y) hs1) (by linarith)).trans ?_
    refine exp_le_exp.2 ?_
    have : 5 * s * (s ^ 2 * log s ^ 5 / log y ^ 2) =
        5 * (s * log s) * (s ^ 2 * log s ^ 4 / log y ^ 2) := by ring
    rw [this]
    have hsl : 0 ≤ s * log s := by positivity
    nlinarith
  have hll : 0 ≤ log (log s) := log_nonneg hls
  calc delta s y * bigM s
        ≤ exp (s * log s / 2) * (3 * exp (c₂ * s - (s * log s + s * log (log s)))) :=
        mul_le_mul hδ hM hB0 (exp_pos _).le
    _ = 3 * exp (s * (c₂ - log s / 2) - s * log (log s)) := by
        rw [mul_left_comm, ← exp_add]; ring_nf
    _ ≤ 3 * exp (|c₂| * exp (2 * |c₂|)) := by
        gcongr
        have := mul_sub_log_div_two_le c₂ hs1
        nlinarith

/-- For `s > ξ(y)` and `log log 3y ≥ 1`: `log y / s ≤ (log log 3y)⁶`. -/
theorem div_le_loglog_pow_six {y s : ℝ} (hy : 1 < y) (hl : 1 ≤ log (log (3 * y)))
    (hs : xi y < s) : log y / s ≤ log (log (3 * y)) ^ 6 := by
  have hL := log_pos hy
  have hξ := TheoremFive.xi_pos hy
  have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos (by linarith) _
  have h1 : log y / xi y = log (log (3 * y)) ^ (11 / 5 : ℝ) := by
    rw [xi]; field_simp
  have h2 : log (log (3 * y)) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (6 : ℝ) :=
    rpow_le_rpow_of_exponent_le hl (by norm_num)
  have h3 : log (log (3 * y)) ^ (6 : ℝ) = log (log (3 * y)) ^ 6 := by
    exact_mod_cast rpow_natCast (log (log (3 * y))) 6
  calc log y / s ≤ log y / xi y := div_le_div_of_nonneg_left hL.le hξ hs.le
    _ ≤ log (log (3 * y)) ^ 6 := by rw [h1, ← h3]; exact h2

/-- `log log 3y ≥ 1` for `y ≥ e^e`. -/
theorem one_le_loglog_of_le {y : ℝ} (hy : exp (exp 1) ≤ y) : 1 ≤ log (log (3 * y)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (exp_pos _) hy
  have h1 : exp 1 ≤ log y := by rw [le_log_iff_exp_le hy0]; exact hy
  have h2 : log y ≤ log (3 * y) := log_le_log hy0 (by linarith)
  rw [le_log_iff_exp_le (by linarith [exp_pos 1])]
  linarith

end Main

open Main

/-- **Corollary to [I71, Theorem 1]**, (1.3): under `(*)`, for `2 ≤ z ≤ y` and
`s = log y / log z`,
`A_k(M; z) < y R_k(z) (1 + (F(s) + (3 - s)⁺)/s + e₁ log log 3k / log y)`.
For `s ≥ 3` this is (1.3) as printed; for `1 ≤ s < 3` the term `(3 - s)⁺` corrects our
convention `F(s) = F(3)` below 3 (see the module docstring). -/
theorem corollary_upper : ∃ e₁ : ℝ, 0 ≤ e₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y z : ℝ),
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z → z ≤ y →
    (siftedCount k M z : ℝ) < y * Rk k z * (1 + (FSieve (log y / log z) +
      max (3 - log y / log z) 0) / (log y / log z) + e₁ * log (log (3 * k)) / log y) := by
  obtain ⟨C, hC, h1⟩ := theorem1_core
  obtain ⟨B, hB, hδB⟩ := exists_delta_mul_bigM_le
  obtain ⟨CF, YF, hCF, hYF, hFL⟩ := fundamental_lemma
  set Y := max YF (exp (exp 1))
  have hY1 : 1 < Y := lt_of_lt_of_le hYF (le_max_left _ _)
  have hLY : 0 < log Y := log_pos hY1
  have hRY := R_pos Y
  have ha := loglog_three_pos
  set e₁ := (C * B + CF + 2 * log Y / R Y + 1) / log (log 3)
  refine ⟨e₁, by positivity, fun k hk M y z hM hz hzy => ?_⟩
  have hy1 : 1 < y := by linarith
  have hL : 0 < log y := log_pos hy1
  have hz1 : 1 < z := by linarith
  have hlz : 0 < log z := log_pos hz1
  have hlzy : log z ≤ log y := log_le_log (by linarith) hzy
  set s := log y / log z with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hlz]; linarith
  have hs0 : 0 < s := by linarith
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div (by linarith) hz1 hL.ne'
  have hls : log y / s = log z := by rw [hs]; field_simp
  rw [show FSieve s + max (3 - s) 0 = mainMaj false s from rfl]
  have hm : 0 ≤ mainMaj false s / s := div_nonneg (mainMaj_nonneg false s) hs0.le
  have hk3 := loglog_three_le hk
  have hT : 0 < y * Rk k z := mul_pos (by linarith) (Rk_pos k z)
  have he : C * B + CF + 2 * log Y / R Y + 1 ≤ e₁ * log (log (3 * k)) := by
    calc C * B + CF + 2 * log Y / R Y + 1 = e₁ * log (log 3) := by
          simp only [e₁]; field_simp
      _ ≤ e₁ * log (log (3 * k)) := by gcongr
  have hCB := mul_nonneg hC hB
  have hlYR : 0 ≤ 2 * log Y / R Y := by positivity
  set E := e₁ * log (log (3 * k)) with hE
  rcases lt_or_ge y Y with hyY | hyY
  · -- bounded `y`: the error term alone exceeds `2y > A`
    have hA := siftedCount_le_add_one (z := z) hM
    have hRk : R Y ≤ Rk k z := (R_antitone (hzy.trans hyY.le)).trans (R_le_Rk k z)
    have hLL : log y ≤ log Y := log_le_log (by linarith) hyY.le
    have h2 : 2 * y ≤ y * Rk k z * (E / log y) := by
      calc 2 * y = y * R Y * (2 * log Y / R Y / log Y) := by field_simp
        _ ≤ y * Rk k z * (E / log y) := by
            gcongr
            · linarith
            · linarith
    have e : y * Rk k z * (1 + mainMaj false s / s + E / log y) =
        y * Rk k z * (1 + mainMaj false s / s) + y * Rk k z * (E / log y) := by ring
    have : 0 ≤ y * Rk k z * (1 + mainMaj false s / s) := by positivity
    rw [e]; linarith
  have hlam := one_le_loglog_of_le (le_trans (le_max_right _ _) hyY)
  have hCE : C * B < E := by linarith
  have hCFE : CF < E := by linarith
  rcases le_or_gt s (xi y) with hsξ | hsξ
  · have hA := (h1 k M y s hy1 hM hsξ).1 hs1
    rw [hzs] at hA
    refine hA.trans_lt (mul_lt_mul_of_pos_left ?_ hT)
    have : C * delta s y * bigM s ≤ C * B := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hδB y s hy1 hs1 hsξ) hC
    have : C * delta s y * bigM s / log y < E / log y :=
      div_lt_div_of_pos_right (by linarith) hL
    linarith
  · have hlog : log z ≤ log (log (3 * y)) ^ 6 := hls ▸ div_le_loglog_pow_six hy1 hlam hsξ
    have hA := (abs_le.1 (hFL k M y z (le_trans (le_max_left _ _) hyY) hM hz hlog)).2
    have h3 : CF * y * Rk k z / log y < y * Rk k z * (E / log y) := by
      rw [show CF * y * Rk k z / log y = y * Rk k z * (CF / log y) by ring]
      exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hCFE hL) hT
    have e : y * Rk k z * (1 + mainMaj false s / s + E / log y) =
        y * Rk k z + y * Rk k z * (mainMaj false s / s) + y * Rk k z * (E / log y) := by ring
    have : 0 ≤ y * Rk k z * (mainMaj false s / s) := by positivity
    rw [e]; linarith

/-- **Corollary to [I71, Theorem 1]**, (1.4): under `(*)`, for `y > 1`, `z ≥ 2` and
`s = log y / log z`, `A_k(M; z) > y R_k(z) (1 - f(s)/s - e₁ log log 3k / log y)`. (For `s < 2`,
i.e. `z > y^{1/2}`, this is trivial, as `f(s) = 2`.) -/
theorem corollary_lower : ∃ e₁ : ℝ, 0 ≤ e₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y z : ℝ),
    1 < y → (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z →
    y * Rk k z * (1 - fSieve (log y / log z) / (log y / log z) -
      e₁ * log (log (3 * k)) / log y) < siftedCount k M z := by
  obtain ⟨C, hC, h1⟩ := theorem1_core
  obtain ⟨B, hB, hδB⟩ := exists_delta_mul_bigM_le
  obtain ⟨CF, YF, hCF, hYF, hFL⟩ := fundamental_lemma
  set Y := max YF (exp (exp 1))
  have hY1 : 1 < Y := lt_of_lt_of_le hYF (le_max_left _ _)
  have hLY : 0 < log Y := log_pos hY1
  have hRY := R_pos Y
  have hRY1 := R_le_one Y
  have ha := loglog_three_pos
  set e₁ := (C * B + CF + 2 * log Y / R Y + 1) / log (log 3)
  refine ⟨e₁, by positivity, fun k hk M y z hy1 hM hz => ?_⟩
  have hL : 0 < log y := log_pos hy1
  have hz1 : 1 < z := by linarith
  have hlz : 0 < log z := log_pos hz1
  set s := log y / log z with hs
  have hs0 : 0 < s := by positivity
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div (by linarith) hz1 hL.ne'
  have hls : log y / s = log z := by rw [hs]; field_simp
  have hk3 := loglog_three_le hk
  have hT : 0 < y * Rk k z := mul_pos (by linarith) (Rk_pos k z)
  have he : C * B + CF + 2 * log Y / R Y + 1 ≤ e₁ * log (log (3 * k)) := by
    calc C * B + CF + 2 * log Y / R Y + 1 = e₁ * log (log 3) := by
          simp only [e₁]; field_simp
      _ ≤ e₁ * log (log (3 * k)) := by gcongr
  have hCB := mul_nonneg hC hB
  have hlYR : log Y ≤ 2 * log Y / R Y := by
    rw [le_div_iff₀ hRY]; nlinarith
  set E := e₁ * log (log (3 * k)) with hE
  have hE0 : 0 ≤ E / log y := div_nonneg (by linarith) hL.le
  have hf0 : 0 ≤ fSieve s / s := div_nonneg (fSieve_nonneg s) hs0.le
  -- a negative bracket gives the claim trivially
  have neg : 1 - fSieve s / s - E / log y < 0 →
      y * Rk k z * (1 - fSieve s / s - E / log y) < siftedCount k M z :=
    fun h ↦ (mul_neg_of_pos_of_neg hT h).trans_le (Nat.cast_nonneg _)
  rcases lt_or_ge s 2 with hs2 | hs2
  · refine neg ?_
    rw [fSieve_of_le_two hs2.le, fSieve_two]
    have : 1 < 2 / s := by rw [lt_div_iff₀ hs0]; linarith
    linarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  rcases lt_or_ge y Y with hyY | hyY
  · refine neg ?_
    have hLL : log y ≤ log Y := log_le_log (by linarith) hyY.le
    have : 1 < E / log y := by rw [lt_div_iff₀ hL]; linarith
    linarith
  have hlam := one_le_loglog_of_le (le_trans (le_max_right _ _) hyY)
  have hCE : C * B < E := by linarith
  have hCFE : CF < E := by linarith
  rcases le_or_gt s (xi y) with hsξ | hsξ
  · have hA := (h1 k M y s hy1 hM hsξ).2 hs2
    rw [hzs] at hA
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ?_ hT) hA
    have : C * delta s y * bigM s ≤ C * B := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hδB y s hy1 hs1 hsξ) hC
    have : C * delta s y * bigM s / log y < E / log y :=
      div_lt_div_of_pos_right (by linarith) hL
    linarith
  · have hlog : log z ≤ log (log (3 * y)) ^ 6 := hls ▸ div_le_loglog_pow_six hy1 hlam hsξ
    have hA := (abs_le.1 (hFL k M y z (le_trans (le_max_left _ _) hyY) hM hz hlog)).1
    have h3 : CF * y * Rk k z / log y < y * Rk k z * (E / log y) := by
      rw [show CF * y * Rk k z / log y = y * Rk k z * (CF / log y) by ring]
      exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hCFE hL) hT
    have e : y * Rk k z * (1 - fSieve s / s - E / log y) =
        y * Rk k z - y * Rk k z * (fSieve s / s) - y * Rk k z * (E / log y) := by ring
    have : 0 ≤ y * Rk k z * (fSieve s / s) := by positivity
    rw [e]; linarith

end IwaniecLinearSieve
