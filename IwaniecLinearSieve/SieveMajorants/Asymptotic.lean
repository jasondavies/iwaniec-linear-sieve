import IwaniecLinearSieve.SieveMajorants.Lemmas

/-!
# The asymptotics of `𝔐` ([I71, Theorem 1 and Lemma 9])

test
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- The comparison exponent `Φ_c(s) = s (log s + log log s - 1 + (log log s + c)/log s)`.
For `c = 0` this is the exponent in [I71, Theorem 1]. -/
noncomputable def asymPhi (c s : ℝ) : ℝ :=
  s * (log s + log (log s) - 1 + (log (log s) + c) / log s)

/-- `Φ_c'(s) = ψ_c(log s)`, where
`ψ_c(L) = L + log L + (log L + c + 1)/L - (log L + c - 1)/L²`. -/
noncomputable def asymPsi (c L : ℝ) : ℝ :=
  L + log L + (log L + c + 1) / L - (log L + c - 1) / L ^ 2

theorem asymPhi_eq_add (c s : ℝ) : asymPhi c s = asymPhi 0 s + c * s / log s := by
  unfold asymPhi; ring

theorem hasDerivAt_asymPhi (c : ℝ) {s : ℝ} (hs : 1 < s) :
    HasDerivAt (asymPhi c) (asymPsi c (log s)) s := by
  have hs0 : s ≠ 0 := by positivity
  have hL : log s ≠ 0 := (log_pos hs).ne'
  have h1 : HasDerivAt log s⁻¹ s := hasDerivAt_log hs0
  have h2 : HasDerivAt (fun x => log (log x)) (s⁻¹ / log s) s := h1.log hL
  have h3 := ((((h1.add h2).sub_const 1).add ((h2.add_const c).div h1 hL)))
  have h4 := (hasDerivAt_id s).mul h3
  refine h4.congr_deriv ?_
  unfold asymPsi
  simp only [id, Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem hasDerivAt_asymPsi (c : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (asymPsi c)
      (1 + 1 / L - (log L + c) / L ^ 2 + (2 * log L + 2 * c - 3) / L ^ 3) L := by
  have hL0 : L ≠ 0 := hL.ne'
  have h1 : HasDerivAt log L⁻¹ L := hasDerivAt_log hL0
  have h2 := ((hasDerivAt_id L).add h1).add (((h1.add_const c).add_const 1).div
    (hasDerivAt_id L) hL0) |>.sub (((h1.add_const c).sub_const 1).div ((hasDerivAt_id L).pow 2)
    (pow_ne_zero 2 hL0))
  refine h2.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  ring

theorem log_le_sub_one_of_two_le {L : ℝ} (hL : 2 ≤ L) : 0 ≤ log L ∧ log L ≤ L - 1 :=
  ⟨log_nonneg (by linarith), log_le_sub_one_of_pos (by linarith)⟩

theorem monotoneOn_asymPsi {c : ℝ} (hc : c ≤ 1) : MonotoneOn (asymPsi c) (Ici 2) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 2)
    (f' := fun L => 1 + 1 / L - (log L + c) / L ^ 2 + (2 * log L + 2 * c - 3) / L ^ 3)
    (fun L hL => ?_)
    (fun L hL => ?_) (fun L hL => ?_)
  · exact (hasDerivAt_asymPsi c (by linarith [hL.out])).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hL
    exact (hasDerivAt_asymPsi c (by linarith [hL.out])).hasDerivWithinAt
  · rw [interior_Ici] at hL
    have hL2 : 2 < L := hL
    have hL0 : 0 < L := by linarith
    obtain ⟨hl0, hl1⟩ := log_le_sub_one_of_two_le hL2.le
    have key : 0 ≤ L ^ 3 + L ^ 2 - (log L + c) * L + (2 * log L + 2 * c - 3) := by
      nlinarith [mul_le_mul_of_nonneg_right hl1 (by linarith : (0 : ℝ) ≤ L - 2),
        mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ L - 2)]
    have e : 1 + 1 / L - (log L + c) / L ^ 2 + (2 * log L + 2 * c - 3) / L ^ 3 =
        (L ^ 3 + L ^ 2 - (log L + c) * L + (2 * log L + 2 * c - 3)) / L ^ 3 := by
      field_simp
    rw [e]
    positivity

theorem two_le_log_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 2 ≤ log x := by
  rw [le_log_iff_exp_le (by linarith)]
  have h := exp_one_lt_d9
  have : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
  rw [this]
  nlinarith [exp_pos 1]

/-- Mean value estimate: for `9 ≤ s`, `s - 1 ≤ x ≤ s` and `c ≤ 1`,
`ψ_c(log(s-1)) (s - x) ≤ Φ_c(s) - Φ_c(x) ≤ ψ_c(log s) (s - x)`. -/
theorem asymPhi_sub_mem {c : ℝ} (hc : c ≤ 1) {s x : ℝ} (hs9 : 9 ≤ s)
    (hx : s - 1 ≤ x) (hxs : x ≤ s) :
    asymPsi c (log (s - 1)) * (s - x) ≤ asymPhi c s - asymPhi c x ∧
      asymPhi c s - asymPhi c x ≤ asymPsi c (log s) * (s - x) := by
  have hs : 2 ≤ log (s - 1) := two_le_log_of_eight_le (by linarith)
  have hs1 : 1 < s - 1 := by linarith
  rcases hxs.lt_or_eq with hxs | rfl
  swap
  · simp
  obtain ⟨y, hy, hy'⟩ := exists_hasDerivAt_eq_slope (asymPhi c) (fun y => asymPsi c (log y)) hxs
    (fun y hy => (hasDerivAt_asymPhi c (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy => hasDerivAt_asymPhi c (by linarith [hy.1]))
  have hsx : 0 < s - x := by linarith
  have e : asymPhi c s - asymPhi c x = asymPsi c (log y) * (s - x) := by
    rw [hy']; field_simp
  rw [e]
  have h1 : log (s - 1) ≤ log y := log_le_log (by linarith) (by linarith [hy.1])
  have h2 : log y ≤ log s := log_le_log (by linarith [hy.1]) hy.2.le
  have hm := monotoneOn_asymPsi hc
  exact ⟨mul_le_mul_of_nonneg_right (hm (mem_Ici.2 hs) (mem_Ici.2 (hs.trans h1)) h1) hsx.le,
    mul_le_mul_of_nonneg_right (hm (mem_Ici.2 (hs.trans h1)) (mem_Ici.2 (hs.trans (h1.trans h2)))
      h2) hsx.le⟩

/-! ### Comparison principle for `A(s) y(s) = ∫_{s-1}^s w(x) y(x) dx` -/

/-- Comparison of a subsolution `f` with a supersolution `g` of
`A(s) y(s) = ∫_{s-1}^s w(x) y(x) dx` (`s ≥ a`), for positive `A`, `w`: if `f < g` on
`[a - 1, a]`, then `f < g` on `[a - 1, ∞)`. -/
theorem lt_of_sub_super {A w f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Ici (a - 1))) (hg : ContinuousOn g (Ici (a - 1)))
    (hw : ContinuousOn w (Ici (a - 1))) (hw0 : ∀ x ≥ a - 1, 0 < w x) (hA : ∀ s ≥ a, 0 < A s)
    (hfs : ∀ s ≥ a, A s * f s ≤ ∫ x in (s - 1)..s, w x * f x)
    (hgs : ∀ s ≥ a, ∫ x in (s - 1)..s, w x * g x ≤ A s * g s)
    (hinit : ∀ x ∈ Icc (a - 1) a, f x < g x) : ∀ s ≥ a - 1, f s < g s := by
  intro s hs
  rcases le_total s a with hsa | hsa
  · exact hinit s ⟨hs, hsa⟩
  have hsub : Ici a ⊆ Ici (a - 1) := Ici_subset_Ici.2 (by linarith)
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => g s - f s) (a₀ := a - 1) (a := a)
    ((hg.sub hf).mono hsub) (fun x hx => (sub_pos.2 (hinit x hx)).le)
    (sub_pos.2 (hinit a ⟨by linarith, le_rfl⟩)) ?_ s hsa
  intro t ht _ hpos
  have hI : Icc (t - 1) t ⊆ Ici (a - 1) := fun x hx => by
    simp only [mem_Ici]; linarith [hx.1]
  have hpos' : ∀ x ∈ Ioo (t - 1) t, 0 < w x * (g x - f x) := by
    intro x hx
    refine mul_pos (hw0 x (by linarith [hx.1])) ?_
    rcases le_total x a with h | h
    · exact sub_pos.2 (hinit x ⟨by linarith [hx.1], h⟩)
    · exact hpos x ⟨h, hx.2⟩
  have hint : 0 < ∫ x in (t - 1)..t, w x * (g x - f x) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        ((hw.mono hI).mul ((hg.sub hf).mono hI))) hpos' (by linarith)
  have hwf : IntervalIntegrable (fun x => w x * f x) volume (t - 1) t :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) ((hw.mono hI).mul (hf.mono hI))
  have hwg : IntervalIntegrable (fun x => w x * g x) volume (t - 1) t :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) ((hw.mono hI).mul (hg.mono hI))
  have e : ∫ x in (t - 1)..t, w x * (g x - f x) =
      (∫ x in (t - 1)..t, w x * g x) - ∫ x in (t - 1)..t, w x * f x := by
    rw [← intervalIntegral.integral_sub hwg hwf]
    congr 1; ext x; ring
  have h1 := hfs t ht.le
  have h2 := hgs t ht.le
  have hAt := hA t ht.le
  have : 0 < A t * (g t - f t) := by nlinarith
  exact (pos_iff_pos_of_mul_pos this).1 hAt |> fun h => by simpa using h

/-! ### The numerical inequalities -/

/-- `(log L)² ≤ L` for `L ≥ 1`. -/
theorem log_sq_le {L : ℝ} (hL : 1 ≤ L) : log L ^ 2 ≤ L := by
  have hL0 : 0 < L := by linarith
  have hy : 0 < √L := sqrt_pos.2 hL0
  -- `log y ≤ y / 2` for `y > 0`
  have h1 : log √L ≤ √L / 2 := by
    have e : log √L = log 2 + log (√L / 2) := by
      rw [← log_mul (by norm_num) (by positivity)]; congr 1; ring
    have := log_le_sub_one_of_pos (show 0 < √L / 2 by positivity)
    linarith [log_two_lt_d9]
  rw [log_sqrt hL0.le] at h1
  have h2 : 0 ≤ log L := log_nonneg hL
  have h3 : log L ≤ √L := by linarith
  calc log L ^ 2 ≤ √L ^ 2 := pow_le_pow_left₀ h2 h3 2
    _ = L := sq_sqrt hL0.le

/-- Subsolution inequality: for `t ≥ 8`, `λ = ψ₁(log t)` satisfies `2 ≤ λ` and `λ t ≤ e^λ`. -/
theorem asymPsi_one_facts {t : ℝ} (ht : 8 ≤ t) :
    2 ≤ asymPsi 1 (log t) ∧ asymPsi 1 (log t) * t ≤ exp (asymPsi 1 (log t)) := by
  set L := log t with hLdef
  have hL : 2 ≤ L := two_le_log_of_eight_le ht
  have hL0 : 0 < L := by linarith
  obtain ⟨hl0, hl1⟩ := log_le_sub_one_of_two_le hL
  set l := log L with hldef
  set lam := asymPsi 1 L with hlam
  have e1 : lam - L = l + ((l + 2) * L - l) / L ^ 2 := by
    rw [hlam]; unfold asymPsi; rw [← hldef]; field_simp; ring
  have h1 : 0 ≤ ((l + 2) * L - l) / L ^ 2 := by
    apply div_nonneg _ (by positivity); nlinarith
  have hlamL : L ≤ lam := by linarith
  refine ⟨by linarith, ?_⟩
  have hlam0 : 0 < lam := by linarith
  -- `log λ ≤ λ - L`
  have e2 : lam - L - l - (lam / L - 1) = (2 * L ^ 2 - (2 * l + 2) * L + l) / L ^ 3 := by
    rw [hlam]; unfold asymPsi; rw [← hldef]; field_simp; ring
  have h2 : 0 ≤ (2 * L ^ 2 - (2 * l + 2) * L + l) / L ^ 3 := by
    apply div_nonneg _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hl1 hL0.le]
  have h3 : log lam ≤ l + (lam / L - 1) := by
    have e : log lam = l + log (lam / L) := by
      rw [hldef, ← log_mul hL0.ne' (by positivity)]; congr 1; field_simp
    rw [e]
    linarith [log_le_sub_one_of_pos (show 0 < lam / L by positivity)]
  have ht0 : 0 < t := by linarith
  calc lam * t = exp (log lam + L) := by
        rw [exp_add, exp_log hlam0, hLdef, exp_log ht0]
    _ ≤ exp lam := exp_le_exp.2 (by linarith)

/-- Supersolution inequality: for `s ≥ e²⁰`, `μ = ψ₋₅(log s)` satisfies `0 < μ` and
`e^μ ≤ μ (s - 2)`. -/
theorem asymPsi_neg_five_facts {s : ℝ} (hs : exp 20 ≤ s) :
    0 < asymPsi (-5) (log s) ∧ exp (asymPsi (-5) (log s)) ≤ asymPsi (-5) (log s) * (s - 2) := by
  have hs0 : 0 < s := lt_of_lt_of_le (exp_pos _) hs
  set L := log s with hLdef
  have hL : 20 ≤ L := by rw [hLdef, le_log_iff_exp_le hs0]; exact hs
  have hL0 : 0 < L := by linarith
  obtain ⟨-, hl1⟩ := log_le_sub_one_of_two_le (show 2 ≤ L by linarith)
  set l := log L with hldef
  have hl : 1 ≤ l := by
    rw [hldef, le_log_iff_exp_le hL0]; linarith [exp_one_lt_d9]
  have hlsq : l ^ 2 ≤ L := log_sq_le (by linarith)
  set u := 1 / L with hu
  have huL : u * L = 1 := by rw [hu]; field_simp
  have hu0 : 0 < u := by positivity
  have hu20 : u ≤ 1 / 20 := by rw [hu]; exact one_div_le_one_div_of_le (by norm_num) hL
  set D := (l - 4) * u - (l - 6) * u ^ 2 with hD
  set mu := asymPsi (-5) L with hmu
  have emu : mu = L + l + D := by
    rw [hmu, hD, hu]; unfold asymPsi; rw [← hldef]; field_simp; ring
  -- `|D| ≤ 1`
  have hlu : l * u ≤ 1 - u := by nlinarith
  have hD1 : D ≤ 1 := by rw [hD]; nlinarith
  have hD2 : -1 ≤ D := by rw [hD]; nlinarith
  have hmu0 : 0 < mu := by rw [emu]; linarith
  -- the key inequality `D (μ - 1) ≤ l - 1`
  have k1 : D * L = l - 4 - (l - 6) * u := by
    rw [hD]; linear_combination (l - 4 - (l - 6) * u) * huL
  have k2 : D * (l - 1) ≤ 1 + 7 * u := by
    have a1 : (l - 4) * (l - 1) * u ≤ 1 := by
      have : (l - 4) * (l - 1) ≤ L := by nlinarith
      nlinarith
    have a2 : -((l - 6) * (l - 1)) * u ^ 2 ≤ 7 * u := by
      have : -((l - 6) * (l - 1)) ≤ 7 * L := by nlinarith
      have hu2 : 0 ≤ u ^ 2 := by positivity
      nlinarith
    have : D * (l - 1) = (l - 4) * (l - 1) * u + -((l - 6) * (l - 1)) * u ^ 2 := by
      rw [hD]; ring
    linarith
  have k3 : D * D ≤ 1 := by nlinarith
  have key : D * (mu - 1) ≤ l - 1 := by
    have : D * (mu - 1) = D * L + D * (l - 1) + D * D := by rw [emu]; ring
    nlinarith
  -- `2 μ ≤ s - 2`
  have hs2 : 2 * mu ≤ s - 2 := by
    have := quadratic_le_exp_of_nonneg hL0.le
    rw [hLdef, exp_log hs0] at this
    rw [emu]; nlinarith
  refine ⟨hmu0, ?_⟩
  have hs2' : 0 < s - 2 := by linarith
  -- lower bounds for `log μ` and `log (s - 2)`
  have hlogmu : l + (1 - L / mu) ≤ log mu := by
    have e : log mu = l + log (mu / L) := by
      rw [hldef, ← log_mul hL0.ne' (by positivity)]; congr 1; field_simp
    rw [e]
    have := one_sub_inv_le_log_of_pos (show 0 < mu / L by positivity)
    rw [inv_div] at this
    linarith
  have hlogs : L + (1 - s / (s - 2)) ≤ log (s - 2) := by
    have e : log (s - 2) = L + log ((s - 2) / s) := by
      rw [hLdef, ← log_mul hs0.ne' (by positivity)]; congr 1; field_simp
    rw [e]
    have := one_sub_inv_le_log_of_pos (show 0 < (s - 2) / s by positivity)
    rw [inv_div] at this
    linarith
  have hb : s / (s - 2) ≤ 1 + 1 / mu := by
    have e : s / (s - 2) = 1 + 2 / (s - 2) := by field_simp; ring
    rw [e, add_le_add_iff_left, div_le_div_iff₀ hs2' hmu0]
    linarith
  have hfin : (L + 1) / mu ≤ L + l + 1 - mu := by
    rw [div_le_iff₀ hmu0]
    have : mu * mu - (L + l + 1) * mu + (L + 1) = D * (mu - 1) - (l - 1) := by
      rw [emu]; ring
    nlinarith
  have hsplit : (L + 1) / mu = L / mu + 1 / mu := by ring
  calc exp mu ≤ exp (log mu + log (s - 2)) := exp_le_exp.2 (by linarith)
    _ = mu * (s - 2) := by rw [exp_add, exp_log hmu0, exp_log hs2']

end IwaniecLinearSieve
