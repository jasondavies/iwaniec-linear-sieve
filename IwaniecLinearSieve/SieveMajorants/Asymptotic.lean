import IwaniecLinearSieve.SieveMajorants.Lemmas

/-!
# The asymptotics of `𝔐` ([I71, Theorem 1 and Lemma 9])

[I71, Theorem 1] states
`𝔐(s) = exp{-s(log s + log log s - 1 + log log s/log s) + O(s/log s)}`, deduced on p. 15 from
the asymptotics of the Dickman function `ϱ` (quoted from Hua's book) via `𝔐(s+2) ≪ ϱ(s) ≪ 𝔐(s)`.
We prove it directly from (3.12), `A(s) 𝔐(s) = ∫_{s-1}^s (1 - 1/(2x²)) 𝔐(x) dx` with
`A(s) = ((s-1)² - 1/2)/s`, by comparison with explicit sub- and supersolutions.

## The argument

Let `L = log s`, `ℓ = log L` and
`Φ_c(s) = s (L + ℓ - 1 + (ℓ + c)/L) = Φ₀(s) + c s/L` (`asymPhi`). Then
`Φ_c'(s) = ψ_c(L) = L + ℓ + (ℓ + c + 1)/L - (ℓ + c - 1)/L²` (`asymPsi`), and `ψ_c` is increasing
on `[2, ∞)` for `c ≤ 4` (`L³ ψ_c'(L) ≥ L³ - L + 3`). By the mean value theorem, for
`s ≥ 9` and `s - 1 ≤ x ≤ s`, `ψ_c(log(s-1)) (s-x) ≤ Φ_c(s) - Φ_c(x) ≤ ψ_c(log s) (s-x)`, hence
`(e^λ - 1)/λ ≤ ∫_{s-1}^s e^{Φ_c(s) - Φ_c(x)} dx ≤ (e^μ - 1)/μ` with `λ = ψ_c(log(s-1))`,
`μ = ψ_c(log s)`.

* Subsolution `h = exp(-Φ₁)`, `s ≥ 9`: with `t = s - 1`, `λ = ψ₁(log t) ≥ 2` and `λ t ≤ e^λ`
  (`asymPsi_one_facts`; from `log λ ≤ ℓ + λ/L - 1` and `2L² - (2ℓ+2)L + ℓ ≥ 0`). As the weight is
  `≥ w₀ = 1 - 1/(2(s-1)²)` and `A(s)/w₀ = (s-1)²/s`, it suffices that
  `λ (s-1)² ≤ s (e^λ - 1)`, which follows (`coefA_mul_le_integral`).
* Supersolution `h = exp(-Φ₋₅)`, `s ≥ e²⁰`: `μ = ψ₋₅(L)` satisfies `e^μ ≤ μ (s - 2)`
  (`asymPsi_neg_five_facts`): writing `μ = L + ℓ + D`, `|D| ≤ 1`, and using
  `log μ ≥ ℓ + 1 - L/μ`, `log(s-2) ≥ L + 1 - s/(s-2)`, `2μ ≤ s - 2`, this reduces to
  `D (μ - 1) ≤ ℓ - 1`, which holds since `ℓ² ≤ L`. As the weight is `≤ 1` and
  `A(s) ≥ s - 2`, `h` is a supersolution (`integral_le_coefA_mul`).

The comparison principle `lt_of_sub_super` (a first-crossing argument) then gives
`κ e^{-Φ₁(s)} ≤ 𝔐(s) ≤ C e^{-Φ₋₅(s)}` for `s ≥ e²⁰`, i.e. `bigM_asymp` with `s₀ = e²⁰`.

## Main results

* `bigM_asymp`: [I71, Theorem 1], the asymptotics of `𝔐`;
* `bigM_add_two_le`, `bigM_lt_integral`: the intermediate claims in [I71, proof of Lemma 9];
* `majG_mul_exp_le`: [I71, Lemma 9], `G_r(s) exp(s log s + s log log s) ≤ exp(c₂ s)`;
  `lemma9`: the two-sided form, with `majG_ge_exp`.
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

theorem monotoneOn_asymPsi {c : ℝ} (hc : c ≤ 4) : MonotoneOn (asymPsi c) (Ici 2) := by
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

/-- Mean value estimate: for `9 ≤ s`, `s - 1 ≤ x ≤ s` and `c ≤ 4`,
`ψ_c(log(s-1)) (s - x) ≤ Φ_c(s) - Φ_c(x) ≤ ψ_c(log s) (s - x)`. -/
theorem asymPhi_sub_mem {c : ℝ} (hc : c ≤ 4) {s x : ℝ} (hs9 : 9 ≤ s)
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

/-! ### Sub- and supersolutions of (3.12) -/

/-- The coefficient `((s-1)² - 1/2)/s` of (3.12). -/
noncomputable def coefA (s : ℝ) : ℝ := ((s - 1) ^ 2 - 1 / 2) / s

theorem continuousOn_asymPhi (c : ℝ) : ContinuousOn (asymPhi c) (Ioi 1) :=
  fun _ hx => (hasDerivAt_asymPhi c hx).continuousAt.continuousWithinAt

theorem continuousOn_exp_neg_asymPhi (c : ℝ) {a : ℝ} (ha : 1 < a) :
    ContinuousOn (fun x => exp (-asymPhi c x)) (Ici a) :=
  ((continuousOn_asymPhi c).mono fun _ hx => lt_of_lt_of_le ha hx).neg.rexp

theorem continuousOn_weight {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => 1 - 1 / (2 * x ^ 2)) (Ici a) := by
  refine continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul
    (continuousOn_id.pow 2)) fun x hx => ?_)
  have : 0 < x := lt_of_lt_of_le ha hx
  positivity

theorem intervalIntegrable_weight_exp (c : ℝ) {s : ℝ} (hs : 3 ≤ s) :
    IntervalIntegrable (fun x => (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi c x)) volume (s - 1) s :=
  ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    (((continuousOn_weight (a := s - 1) (by linarith)).mul
      (continuousOn_exp_neg_asymPhi c (a := s - 1) (by linarith))).mono Icc_subset_Ici_self)

/-- `∫_{s-1}^s e^{-λ(x-(s-1))} dx = (1 - e^{-λ})/λ`. -/
theorem integral_exp_neg_mul_unit' (s : ℝ) {l : ℝ} (hl : l ≠ 0) :
    ∫ x in (s - 1)..s, exp (-(l * (x - (s - 1)))) = (1 - exp (-l)) / l := by
  have := integral_exp_neg_mul_unit (s - 1) hl
  rwa [sub_add_cancel] at this

/-- `exp(-Φ₁)` is a subsolution of (3.12) for `s ≥ 9`. -/
theorem coefA_mul_le_integral {s : ℝ} (hs : 9 ≤ s) :
    coefA s * exp (-asymPhi 1 s) ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi 1 x) := by
  obtain ⟨hl2, hlt⟩ := asymPsi_one_facts (t := s - 1) (by linarith)
  set l := asymPsi 1 (log (s - 1)) with hl
  set H := exp (-asymPhi 1 s) with hH
  have hl0 : 0 < l := by linarith
  have hs0 : 0 < s := by linarith
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2) with hw₀
  have hpt : ∀ x ∈ Icc (s - 1) s, w₀ * (H * exp l) * exp (-(l * (x - (s - 1)))) ≤
      (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi 1 x) := by
    intro x hx
    have hwx : w₀ ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
        one_div_le_one_div_of_le (by nlinarith) (by nlinarith [hx.1])
      rw [hw₀]; linarith
    have hhx : H * exp l * exp (-(l * (x - (s - 1)))) ≤ exp (-asymPhi 1 x) := by
      rw [hH, ← exp_add, ← exp_add, exp_le_exp]
      have := (asymPhi_sub_mem (c := 1) (by norm_num) hs hx.1 hx.2).1
      linarith
    rw [mul_assoc]
    exact mul_le_mul hwx hhx (by positivity) (weight_mem (by linarith [hx.1])).1.le
  have hint : w₀ * (H * exp l) * ((1 - exp (-l)) / l) ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi 1 x) := by
    rw [← integral_exp_neg_mul_unit' s hl0.ne', ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun x =>
        w₀ * (H * exp l) * exp (-(l * (x - (s - 1))))).intervalIntegrable _ _)
      (intervalIntegrable_weight_exp 1 (by linarith)) hpt
  refine le_trans ?_ hint
  have ea : exp l * (1 - exp (-l)) = exp l - 1 := by
    rw [mul_sub, mul_one, ← exp_add]; simp
  have e : w₀ * (H * exp l) * ((1 - exp (-l)) / l) =
      H * (((s - 1) ^ 2 - 1 / 2) * (exp l - 1) / ((s - 1) ^ 2 * l)) := by
    rw [← ea, hw₀]
    have : s - 1 ≠ 0 := by linarith
    field_simp
  rw [e, coefA, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  have hr : 0 ≤ (s - 1) ^ 2 - 1 / 2 := by nlinarith
  rw [div_le_div_iff₀ hs0 (mul_pos (by nlinarith) hl0)]
  have : l * (s - 1) ^ 2 ≤ s * (exp l - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hr]

/-- `exp(-Φ₋₅)` is a supersolution of (3.12) for `s ≥ e²⁰`. -/
theorem integral_le_coefA_mul {s : ℝ} (hs : exp 20 ≤ s) :
    ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi (-5) x) ≤
      coefA s * exp (-asymPhi (-5) s) := by
  have hs9 : 9 ≤ s := by linarith [add_one_le_exp 20]
  obtain ⟨hm0, hme⟩ := asymPsi_neg_five_facts hs
  set m := asymPsi (-5) (log s) with hm
  set H := exp (-asymPhi (-5) s) with hH
  have hs0 : 0 < s := by linarith
  have hpt : ∀ x ∈ Icc (s - 1) s, (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi (-5) x) ≤
      H * exp m * exp (-(m * (x - (s - 1)))) := by
    intro x hx
    have hw := weight_mem (x := x) (by linarith [hx.1])
    have hhx : exp (-asymPhi (-5) x) ≤ H * exp m * exp (-(m * (x - (s - 1)))) := by
      rw [hH, ← exp_add, ← exp_add, exp_le_exp]
      have := (asymPhi_sub_mem (c := -5) (by norm_num) hs9 hx.1 hx.2).2
      linarith
    calc (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi (-5) x) ≤ 1 * exp (-asymPhi (-5) x) :=
          mul_le_mul_of_nonneg_right hw.2 (exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact hhx
  have hint : ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * exp (-asymPhi (-5) x) ≤
      H * exp m * ((1 - exp (-m)) / m) := by
    rw [← integral_exp_neg_mul_unit' s hm0.ne', ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_weight_exp (-5) (by linarith))
      ((by fun_prop : Continuous fun x =>
        H * exp m * exp (-(m * (x - (s - 1))))).intervalIntegrable _ _) hpt
  refine hint.trans ?_
  have ea : exp m * ((1 - exp (-m)) / m) = (exp m - 1) / m := by
    rw [mul_div_assoc', mul_sub, mul_one, ← exp_add]; simp
  rw [mul_assoc, ea, coefA, mul_comm (((s - 1) ^ 2 - 1 / 2) / s)]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  rw [div_le_div_iff₀ hm0 hs0]
  nlinarith

/-! ### Comparison of `𝔐` with `exp(-Φ_c)` -/

/-- (3.12) in the form `A(s) 𝔐(s) = ∫_{s-1}^s (1 - 1/(2x²)) 𝔐(x) dx`. -/
theorem coefA_mul_bigM {s : ℝ} (hs : 3 ≤ s) :
    coefA s * bigM s = ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
  rw [coefA, div_mul_eq_mul_div, bigM_integral_identity hs]

theorem coefA_pos {s : ℝ} (hs : 3 ≤ s) : 0 < coefA s := by
  unfold coefA
  have : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
  positivity

theorem asymPhi_nonneg {c : ℝ} (hc : 0 ≤ c) {s : ℝ} (hs : 8 ≤ s) : 0 ≤ asymPhi c s := by
  have hL := two_le_log_of_eight_le hs
  have hl := (log_le_sub_one_of_two_le hL).1
  unfold asymPhi
  have : 0 ≤ (log (log s) + c) / log s := by positivity
  have : 0 ≤ s := by linarith
  have : 0 ≤ log s + log (log s) - 1 + (log (log s) + c) / log s := by linarith
  positivity

/-- Lower bound: `𝔐(s) ≥ κ exp(-Φ₁(s))` for `s ≥ 9`. -/
theorem bigM_ge_exp_asymPhi : ∃ κ > 0, ∀ s ≥ 9, κ * exp (-asymPhi 1 s) ≤ bigM s := by
  set κ := bigM 10 / 2 with hκ
  have hκ0 : 0 < κ := by have := bigM_pos 10; positivity
  refine ⟨κ, hκ0, fun s hs => ?_⟩
  have := lt_of_sub_super (A := coefA) (w := fun x => 1 - 1 / (2 * x ^ 2))
    (f := fun x => κ * exp (-asymPhi 1 x)) (g := bigM) (a := 10)
    (continuousOn_const.mul (continuousOn_exp_neg_asymPhi 1 (by norm_num)))
    continuous_bigM.continuousOn (continuousOn_weight (by norm_num))
    (fun x hx => (weight_mem (by linarith [hx.le])).1) (fun s hs => coefA_pos (by linarith))
    (fun s hs => ?_) (fun s hs => (coefA_mul_bigM (by linarith)).ge) (fun x hx => ?_) s
    (by norm_num; linarith)
  · exact this.le
  · rw [intervalIntegral.integral_congr (g := fun x => κ * ((1 - 1 / (2 * x ^ 2)) *
      exp (-asymPhi 1 x))) (fun x _ => by simp only; ring), intervalIntegral.integral_const_mul,
      mul_left_comm]
    exact mul_le_mul_of_nonneg_left (coefA_mul_le_integral (by linarith)) hκ0.le
  · have h1 : exp (-asymPhi 1 x) ≤ 1 := by
      rw [exp_le_one_iff, neg_nonpos]
      exact asymPhi_nonneg zero_le_one (by norm_num at hx; linarith [hx.1])
    have h2 : bigM 10 ≤ bigM x := bigM_antitone hx.2
    have h3 := bigM_pos 10
    show κ * exp (-asymPhi 1 x) < bigM x
    nlinarith

/-- Upper bound: `𝔐(s) ≤ C exp(-Φ₋₅(s))` for `s ≥ e²⁰`. -/
theorem bigM_le_exp_asymPhi : ∃ C, ∀ s ≥ exp 20, bigM s ≤ C * exp (-asymPhi (-5) s) := by
  set a := exp 20 with ha
  have ha21 : 21 ≤ a := by linarith [add_one_le_exp 20]
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith : a - 1 ≤ a))
    (((continuousOn_asymPhi (-5)).mono fun x hx => by
      simp only [mem_Ioi]; linarith [hx.1]) : ContinuousOn (asymPhi (-5)) (Icc (a - 1) a))
  set C := 4 * exp (asymPhi (-5) x₀) with hC
  refine ⟨C, fun s hs => ?_⟩
  have := lt_of_sub_super (A := coefA) (w := fun x => 1 - 1 / (2 * x ^ 2))
    (f := bigM) (g := fun x => C * exp (-asymPhi (-5) x)) (a := a)
    continuous_bigM.continuousOn
    (continuousOn_const.mul (continuousOn_exp_neg_asymPhi (-5) (by linarith)))
    (continuousOn_weight (by linarith))
    (fun x hx => (weight_mem (by linarith [hx.le])).1) (fun s hs => coefA_pos (by linarith))
    (fun s hs => (coefA_mul_bigM (by linarith)).le) (fun s hs => ?_) (fun x hx => ?_) s
    (by linarith)
  · exact this.le
  · rw [intervalIntegral.integral_congr (g := fun x => C * ((1 - 1 / (2 * x ^ 2)) *
      exp (-asymPhi (-5) x))) (fun x _ => by simp only; ring), intervalIntegral.integral_const_mul,
      mul_left_comm]
    exact mul_le_mul_of_nonneg_left (integral_le_coefA_mul hs) (by positivity)
  · show bigM x < C * exp (-asymPhi (-5) x)
    have h1 : asymPhi (-5) x ≤ asymPhi (-5) x₀ := hmax hx
    have h2 : 4 ≤ C * exp (-asymPhi (-5) x) := by
      rw [hC, mul_assoc, ← exp_add]
      have : 1 ≤ exp (asymPhi (-5) x₀ + -asymPhi (-5) x) := one_le_exp (by linarith)
      linarith
    linarith [bigM_le_three x]

/-- **The asymptotics of `𝔐`** ([I71, Theorem 1]):
`𝔐(s) = exp{-s (log s + log log s - 1 + log log s / log s) + O(s / log s)}`. -/
theorem bigM_asymp : ∃ C s₀ : ℝ, ∀ s ≥ s₀,
    |Real.log (bigM s) + s * (Real.log s + Real.log (Real.log s) - 1 +
      Real.log (Real.log s) / Real.log s)| ≤ C * s / Real.log s := by
  obtain ⟨κ, hκ, hlow⟩ := bigM_ge_exp_asymPhi
  obtain ⟨C, hup⟩ := bigM_le_exp_asymPhi
  refine ⟨|log κ| + |log C| + 5, exp 20, fun s hs => ?_⟩
  have hs9 : 9 ≤ s := by linarith [add_one_le_exp 20]
  have hs0 : 0 < s := by linarith
  have hL : 0 < log s := log_pos (by linarith)
  have hsL : 1 ≤ s / log s := by
    rw [le_div_iff₀ hL, one_mul]; linarith [log_le_sub_one_of_pos hs0]
  have hM := bigM_pos s
  have e0 : s * (log s + log (log s) - 1 + log (log s) / log s) = asymPhi 0 s := by
    unfold asymPhi; rw [add_zero]
  rw [e0]
  have h1 := hlow s hs9
  have h2 := hup s hs
  have hC : 0 < C := by
    by_contra h
    push Not at h
    have : C * exp (-asymPhi (-5) s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (exp_pos _).le
    linarith
  -- logarithmic forms
  have l1 : log κ - asymPhi 1 s ≤ log (bigM s) := by
    have := log_le_log (by positivity) h1
    rwa [log_mul hκ.ne' (exp_pos _).ne', log_exp, ← sub_eq_add_neg] at this
  have l2 : log (bigM s) ≤ log C - asymPhi (-5) s := by
    have := log_le_log hM h2
    rwa [log_mul hC.ne' (exp_pos _).ne', log_exp, ← sub_eq_add_neg] at this
  rw [asymPhi_eq_add 1 s] at l1
  rw [asymPhi_eq_add (-5) s] at l2
  have e1 : (|log κ| + |log C| + 5) * s / log s =
      (|log κ| + |log C|) * (s / log s) + 5 * (s / log s) := by ring
  have e2 : 1 * s / log s = s / log s := by ring
  have e3 : -5 * s / log s = -(5 * (s / log s)) := by ring
  rw [e2] at l1
  rw [e3] at l2
  rw [e1, abs_le]
  have k1 := neg_abs_le (log κ)
  have k2 := le_abs_self (log C)
  have k3 : 0 ≤ |log κ| := abs_nonneg _
  have k4 : 0 ≤ |log C| := abs_nonneg _
  constructor <;> nlinarith

/-- [I71, p. 15]: `𝔐(s+2) ≤ exp{-s(log s + log log s - 1 + log log s/log s + O(1/log s))}`. -/
theorem bigM_add_two_le : ∃ C s₀ : ℝ, ∀ s ≥ s₀, bigM (s + 2) ≤
    exp (-(s * (log s + log (log s) - 1 + log (log s) / log s)) + C * s / log s) := by
  obtain ⟨C, s₀, h⟩ := bigM_asymp
  refine ⟨C, s₀, fun s hs => ?_⟩
  have h1 := (abs_le.1 (h s hs)).2
  calc bigM (s + 2) ≤ bigM s := bigM_antitone (by linarith)
    _ = exp (log (bigM s)) := (exp_log (bigM_pos s)).symm
    _ ≤ _ := exp_le_exp.2 (by linarith)

/-- [I71, proof of Lemma 9]: `𝔐(s) < (1/(s-2)) ∫_{s-1}^s 𝔐(x) dx` for `s ≥ 3`. -/
theorem bigM_lt_integral {s : ℝ} (hs : 3 ≤ s) :
    bigM s < 1 / (s - 2) * ∫ x in (s - 1)..s, bigM x := by
  have hs2 : 0 < s - 2 := by linarith
  have hI : ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x < ∫ x in (s - 1)..s, bigM x := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) (continuousOn_weight_mul continuous_bigM (by linarith))
      continuous_bigM.continuousOn (fun x hx => ?_) ⟨s, ⟨by linarith, le_rfl⟩, ?_⟩
    · have hw := weight_mem (x := x) (by linarith [hx.1])
      nlinarith [bigM_pos x]
    · have : 0 < 1 / (2 * s ^ 2) := by positivity
      nlinarith [bigM_pos s]
  have hA : s - 2 ≤ coefA s := by
    unfold coefA
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  rw [← coefA_mul_bigM hs] at hI
  rw [one_div_mul_eq_div, lt_div_iff₀ hs2]
  nlinarith [bigM_pos s]

/-! ### Lemma 9 -/

/-- [I71, Lemma 9]: `G_r(s) exp(s log s + s log log s) ≤ exp(c₂ s)` for `s ≥ 3`. -/
theorem majG_mul_exp_le : ∃ c₂ : ℝ, ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
    majG r s * exp (s * log s + s * log (log s)) ≤ exp (c₂ * s) := by
  obtain ⟨C, hC⟩ := bigM_le_exp_asymPhi
  refine ⟨47 + |log C|, fun r s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have hG := (majG_mem r s).2
  have hGpos := majG_pos r s
  have hL : 1 ≤ log s := one_le_log_of_three_le hs
  have hl0 : 0 ≤ log (log s) := log_nonneg hL
  rcases le_total s (exp 20) with h20 | h20
  · -- bounded range: `G_r ≤ 2 ≤ e^s` and `s log s + s log log s ≤ 40 s`
    have hL20 : log s ≤ 20 := by rw [log_le_iff_le_exp hs0]; exact h20
    have hl20 : log (log s) ≤ 20 := by
      linarith [log_le_sub_one_of_pos (show 0 < log s by linarith)]
    have h1 : majG r s ≤ exp s := by
      linarith [majG_le_two r s, add_one_le_exp s]
    have h2 : s * log s + s * log (log s) ≤ 40 * s := by nlinarith
    calc majG r s * exp (s * log s + s * log (log s)) ≤ exp s * exp (40 * s) :=
          mul_le_mul h1 (exp_le_exp.2 h2) (exp_pos _).le (exp_pos _).le
      _ = exp (41 * s) := by rw [← exp_add]; ring_nf
      _ ≤ exp ((47 + |log C|) * s) := exp_le_exp.2 (by nlinarith [abs_nonneg (log C)])
  · have hM := hC s h20
    have hCpos : 0 < C := by
      by_contra h
      push Not at h
      have : C * exp (-asymPhi (-5) s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (exp_pos _).le
      linarith [bigM_pos s]
    have hphi : s * log s + s * log (log s) - 6 * s ≤ asymPhi (-5) s := by
      unfold asymPhi
      have : -5 ≤ (log (log s) + -5) / log s := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      nlinarith
    have hC' : C ≤ exp (|log C| * s) := by
      calc C = exp (log C) := (exp_log hCpos).symm
        _ ≤ exp (|log C| * s) := exp_le_exp.2 (by
          nlinarith [le_abs_self (log C), abs_nonneg (log C)])
    calc majG r s * exp (s * log s + s * log (log s))
        ≤ C * exp (-asymPhi (-5) s) * exp (s * log s + s * log (log s)) :=
          mul_le_mul_of_nonneg_right (by linarith [bigM_pos s]) (exp_pos _).le
      _ = C * exp (s * log s + s * log (log s) - asymPhi (-5) s) := by
          rw [mul_assoc, ← exp_add]; ring_nf
      _ ≤ exp (|log C| * s) * exp (6 * s) :=
          mul_le_mul hC' (exp_le_exp.2 (by linarith)) (exp_pos _).le (exp_pos _).le
      _ = exp ((6 + |log C|) * s) := by rw [← exp_add]; ring_nf
      _ ≤ exp ((47 + |log C|) * s) := exp_le_exp.2 (by nlinarith)

/-- [I71, Lemma 9], two-sided: `exp(-c₂ s) ≤ G_r(s) exp(s log s + s log log s) ≤ exp(c₂ s)`
for `s ≥ 3`. -/
theorem lemma9 : ∃ c₂ : ℝ, ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
    exp (-(c₂ * s)) ≤ majG r s * exp (s * log s + s * log (log s)) ∧
      majG r s * exp (s * log s + s * log (log s)) ≤ exp (c₂ * s) := by
  obtain ⟨c, hc⟩ := majG_ge_exp
  obtain ⟨c₂, hc₂⟩ := majG_mul_exp_le
  refine ⟨max c c₂, fun r s hs => ⟨?_, ?_⟩⟩
  · have h := mul_le_mul_of_nonneg_right (hc r s hs) (exp_pos (s * log s + s * log (log s))).le
    rw [← exp_add] at h
    refine le_trans (exp_le_exp.2 ?_) h
    nlinarith [le_max_left c c₂]
  · exact (hc₂ r s hs).trans (exp_le_exp.2 (by nlinarith [le_max_right c c₂]))

end IwaniecLinearSieve
