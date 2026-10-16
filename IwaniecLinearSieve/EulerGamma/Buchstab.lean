import IwaniecLinearSieve.SieveMajorants.Delay

/-!
# Buchstab's function

Buchstab's function `ω` is the continuous function on `[1, ∞)` with

* `u ω(u) = 1` for `1 ≤ u ≤ 2`,
* `(u ω(u))' = ω(u - 1)` for `u > 2`.

We construct it with the delay-equation solver `Delay.sol` (applied to `V(x) = (x-1) ω(x-1)`,
which satisfies `V = 1` on `(-∞, 3]` and `V'(x) = V(x-1)/(x-2)` for `x > 3`), prove that it is
the unique such function (`eqOn_buchstab`, allowing countably many exceptional points for the
derivative), that `|ω| ≤ 1`, and compute its Laplace transform: for `s > 0`,

`1 + ∫_1^∞ e^{-su} ω(u) du = exp(E(s))`, `E(s) = -γ - ∫_0^s log t e^{-t} dt - e^{-s} log s`

(`E(s)` is the exponential integral `∫_s^∞ e^{-t}/t dt`; `γ = -∫_0^∞ log t e^{-t} dt` is
`Real.eulerMascheroniConstant_eq_neg_integral_log`). Letting `s → 0⁺` gives the theorem of
de Bruijn: if `ω - c` is integrable on `(1, ∞)` (in particular if `ω → c` fast enough), then
`c = e^{-γ}` (`eq_exp_neg_of_integrableOn_buchstab_sub`). The convergence of `ω` itself is
proved in `IwaniecLinearSieve.EulerGamma.LemmaFive` (`tendsto_buchstab`), following [I71,
Lemma 5]: `ω` is Iwaniec's `w = (2s - W(s))/(s (3 + F(3)))`, and `W(s) = O(s e^{-s})`.
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- The coefficient of the delay equation for `V(x) = (x-1) ω(x-1)`: `1/(x-2)` for `x ≥ 3`. -/
noncomputable def buchstabKernel (x : ℝ) : ℝ := 1 / max (x - 2) 1

/-- `V(x) = (x-1) ω(x-1)`: `V = 1` on `(-∞, 3]` and `V'(x) = V(x-1)/(x-2)` for `x > 3`. -/
noncomputable def buchstabAux : ℝ → ℝ := Delay.sol buchstabKernel 1

/-- Buchstab's function `ω`: `ω(u) = 1/u` for `u ≤ 2` and `(u ω(u))' = ω(u-1)` for `u > 2`. -/
noncomputable def buchstab (u : ℝ) : ℝ := buchstabAux (u + 1) / u

theorem continuous_buchstabKernel : Continuous buchstabKernel :=
  continuous_const.div ((continuous_sub_right 2).max continuous_const) fun _ =>
    (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

theorem continuous_buchstabAux : Continuous buchstabAux :=
  Delay.continuous_sol continuous_buchstabKernel continuous_const

theorem buchstab_of_le_two {u : ℝ} (hu : u ≤ 2) : buchstab u = 1 / u := by
  rw [buchstab, buchstabAux, Delay.sol_of_le (by linarith)]
  rfl

theorem mul_buchstab {u : ℝ} (hu : u ≠ 0) : u * buchstab u = buchstabAux (u + 1) := by
  rw [buchstab, mul_div_cancel₀ _ hu]

theorem continuousOn_buchstab : ContinuousOn buchstab (Ioi 0) :=
  ((continuous_buchstabAux.comp (continuous_id.add continuous_const)).continuousOn).div
    continuousOn_id fun _ hu => (mem_Ioi.1 hu).ne'

theorem measurable_buchstab : Measurable buchstab :=
  (continuous_buchstabAux.measurable.comp (measurable_add_const 1)).div measurable_id

/-- The delay equation `(u ω(u))' = ω(u - 1)` for `u > 2`. -/
theorem hasDerivAt_mul_buchstab {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun u => u * buchstab u) (buchstab (u - 1)) u := by
  have h := (Delay.hasDerivAt_sol (y₀ := (1 : ℝ → ℝ)) continuous_buchstabKernel continuous_const
    (show (3 : ℝ) < u + 1 by linarith)).comp_add_const u 1
  have hk : buchstabKernel (u + 1) = 1 / (u - 1) := by
    rw [buchstabKernel, max_eq_left (by linarith)]
    ring_nf
  have hb : buchstab (u - 1) = buchstabKernel (u + 1) * buchstabAux u := by
    rw [hk, buchstab, sub_add_cancel]
    ring
  rw [hb]
  rw [add_sub_cancel_right] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < u by linarith)] with x hx
  exact mul_buchstab (mem_Ioi.1 hx).ne'

/-- The integrated form `u ω(u) = 1 + ∫_2^u ω(t - 1) dt` for `u ≥ 2`. -/
theorem mul_buchstab_eq_integral {u : ℝ} (hu : 2 ≤ u) :
    u * buchstab u = 1 + ∫ t in (2 : ℝ)..u, buchstab (t - 1) := by
  have hc : ContinuousOn (fun t => buchstab (t - 1)) (Icc 2 u) :=
    continuousOn_buchstab.comp (continuousOn_id.sub continuousOn_const) fun t ht => by
      simp only [mem_Ioi]; linarith [ht.1]
  have hcm : ContinuousOn (fun t => t * buchstab t) (Icc 2 u) :=
    continuousOn_id.mul (continuousOn_buchstab.mono fun t ht => by
      simp only [mem_Ioi]; linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hcm
    (fun t ht => hasDerivAt_mul_buchstab ht.1) (hc.intervalIntegrable_of_Icc hu),
    buchstab_of_le_two le_rfl]
  ring

theorem abs_buchstab_le {u : ℝ} (hu : 1 ≤ u) : |buchstab u| ≤ 1 := by
  suffices h : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ n + 2 → |buchstab u| ≤ 1 from
    h ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])
  intro n
  induction n with
  | zero =>
    intro u hu1 hu2
    rw [buchstab_of_le_two (by simpa using hu2), abs_of_pos (by positivity)]
    exact div_le_one_of_le₀ hu1 (by linarith)
  | succ n ih =>
    intro u hu1 hu2
    rcases le_total u (n + 2) with h | h
    · exact ih u hu1 h
    have hu2' : 2 ≤ u := le_trans (by linarith [n.cast_nonneg (α := ℝ)]) h
    have hI : ‖∫ t in (2 : ℝ)..u, buchstab (t - 1)‖ ≤ 1 * |u - 2| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le hu2'] at ht
      push_cast at hu2
      exact ih (t - 1) (by linarith [ht.1]) (by linarith [ht.2])
    rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (show 0 ≤ u - 2 by linarith)] at hI
    have hu0 : 0 < u := by linarith
    have : |u * buchstab u| ≤ u := by
      rw [mul_buchstab_eq_integral hu2']
      calc |1 + ∫ t in (2 : ℝ)..u, buchstab (t - 1)| ≤ 1 + (u - 2) :=
            (abs_add_le _ _).trans (by rw [abs_one]; linarith)
        _ ≤ u := by linarith
    rw [abs_mul, abs_of_pos hu0] at this
    exact le_of_mul_le_mul_left (by linarith) hu0

/-- Uniqueness: a function continuous on `[1, ∞)` with `φ(u) = 1/u` on `[1, 2]` and
`(u φ(u))' = φ(u - 1)` for `u > 2` (except at countably many points) is `ω`. -/
theorem eqOn_buchstab {φ : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable) (hφ : ContinuousOn φ (Ici 1))
    (h12 : ∀ u ∈ Icc (1 : ℝ) 2, φ u = 1 / u)
    (hd : ∀ u, 2 < u → u ∉ S → HasDerivAt (fun u => u * φ u) (φ (u - 1)) u) :
    EqOn φ buchstab (Ici 1) := by
  suffices h : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ n + 2 → φ u = buchstab u from
    fun u hu => h ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])
  intro n
  induction n with
  | zero =>
    intro u hu1 hu2
    rw [h12 u ⟨hu1, by simpa using hu2⟩, buchstab_of_le_two (by simpa using hu2)]
  | succ n ih =>
    intro u hu1 hu2
    rcases le_total u (n + 2) with h | h
    · exact ih u hu1 h
    push_cast at hu2
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    set d : ℝ → ℝ := fun t => t * φ t - t * buchstab t
    have hcont : ContinuousOn d (Icc (n + 2) u) := by
      have hsub : Icc ((n : ℝ) + 2) u ⊆ Ici 1 := fun t ht => by
        simp only [mem_Ici]; linarith [ht.1]
      exact (continuousOn_id.mul (hφ.mono hsub)).sub (continuousOn_id.mul
        (continuousOn_buchstab.mono fun t ht => by simp only [mem_Ioi]; linarith [(hsub ht).out]))
    have hderiv : ∀ t ∈ Ioo ((n : ℝ) + 2) u \ S, HasDerivAt d 0 t := by
      intro t ⟨ht, htS⟩
      have h2 : 2 < t := by linarith [ht.1]
      have := (hd t h2 htS).sub (hasDerivAt_mul_buchstab h2)
      rwa [ih (t - 1) (by linarith [ht.1]) (by linarith [ht.2]), sub_self] at this
    have := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le d (fun _ => 0) h hS
      hcont hderiv intervalIntegrable_const
    simp only [intervalIntegral.integral_zero] at this
    have h0 : d (n + 2) = 0 := by
      simp only [d, ih (n + 2) (by linarith) le_rfl, sub_self]
    have hu0 : u ≠ 0 := by linarith
    have : u * φ u = u * buchstab u := by
      have := this.symm
      rw [h0, sub_zero] at this
      exact sub_eq_zero.1 this
    exact mul_left_cancel₀ hu0 this

/-! ### The Laplace transform of `ω` -/

theorem integrableOn_log_mul_exp_neg : IntegrableOn (fun t => log t * exp (-t)) (Ioi 0) := by
  refine Integrable.mono' (g := fun x => (2 * x ^ (-(1 : ℝ) / 2) + x) * exp (-x)) ?_ ?_ ?_
  · simp only [add_mul, mul_assoc]
    refine (Integrable.const_mul ?_ _).add ?_
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (-1 : ℝ) / 2) one_pos one_pos
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (1 : ℝ)) one_pos one_pos
  · exact (measurable_log.mul (measurable_neg.exp)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_exp]
    gcongr
    rw [abs_le]
    constructor
    · have := neg_rpow_div_le_log hx.le one_half_pos
      have h2 : 0 ≤ x ^ (-(1 : ℝ) / 2) := by positivity
      rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring] at h2 ⊢
      linarith
    · have := log_le_self hx.le
      have h2 : 0 ≤ x ^ (-(1 : ℝ) / 2) := by positivity
      linarith

theorem intervalIntegrable_log_mul_exp_neg {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun t => log t * exp (-t)) volume 0 s :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).2
    (integrableOn_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self)

/-- The exponential integral `E₁(s) = ∫_s^∞ e^{-t}/t dt`, written as
`-γ - ∫_0^s log t e^{-t} dt - e^{-s} log s` (integration by parts). -/
noncomputable def expIntegralOne (s : ℝ) : ℝ :=
  -eulerMascheroniConstant - (∫ t in (0 : ℝ)..s, log t * exp (-t)) - exp (-s) * log s

theorem hasDerivAt_expIntegralOne {s : ℝ} (hs : 0 < s) :
    HasDerivAt expIntegralOne (-(exp (-s) / s)) s := by
  have hc : ContinuousOn (fun t => log t * exp (-t)) (Ioi 0) :=
    (continuousOn_log.mono fun _ hx => (mem_Ioi.1 hx).ne').mul
      (continuous_exp.comp continuous_neg).continuousOn
  have h1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, log t * exp (-t)) (log s * exp (-s)) s :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_log_mul_exp_neg hs.le)
      (hc.stronglyMeasurableAtFilter isOpen_Ioi s hs) (hc.continuousAt (Ioi_mem_nhds hs))
  have h2 : HasDerivAt (fun u => exp (-u) * log u) (exp (-s) * (-1) * log s + exp (-s) * s⁻¹) s :=
    ((hasDerivAt_neg s).exp).mul (hasDerivAt_log hs.ne')
  have h := ((hasDerivAt_const s (-eulerMascheroniConstant)).sub h1).sub h2
  rw [show -(exp (-s) / s) = 0 - log s * exp (-s) - (exp (-s) * (-1) * log s + exp (-s) * s⁻¹)
    by ring]
  exact h

theorem tendsto_expIntegralOne_atTop : Tendsto expIntegralOne atTop (𝓝 0) := by
  have h1 : Tendsto (fun s => ∫ t in (0 : ℝ)..s, log t * exp (-t)) atTop
      (𝓝 (-eulerMascheroniConstant)) := by
    rw [eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
    exact intervalIntegral_tendsto_integral_Ioi 0 integrableOn_log_mul_exp_neg tendsto_id
  have h2 : Tendsto (fun s => exp (-s) * log s) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [eventually_ge_atTop 1] with s hs
      exact mul_nonneg (exp_pos _).le (log_nonneg hs)
    · filter_upwards [eventually_ge_atTop 1] with s hs
      rw [rpow_one, neg_one_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (log_le_self (by linarith)) (exp_pos _).le
  have := ((tendsto_const_nhds (x := -eulerMascheroniConstant)).sub h1).sub h2
  rw [show (0 : ℝ) = -eulerMascheroniConstant - -eulerMascheroniConstant - 0 by ring]
  exact this

theorem tendsto_expIntegralOne_add_log :
    Tendsto (fun s => expIntegralOne s + log s) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun s => ∫ t in (0 : ℝ)..s, log t * exp (-t)) (𝓝[>] 0) (𝓝 0) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_log_mul_exp_neg zero_le_one) (a := 0) (by simp)
    rw [uIcc_of_le zero_le_one] at hcont
    have h := (hcont 0 (by simp)).tendsto
    simp only [intervalIntegral.integral_same] at h
    exact h.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT one_pos))
  have h2 : Tendsto (fun s => (1 - exp (-s)) * log s) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun x => log x * x) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    refine squeeze_zero_norm' ?_ (by simpa using h.norm)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    rw [norm_mul, mul_comm (‖_‖), Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (by simpa using hs.le), abs_of_pos hs]
    linarith [add_one_le_exp (-s)]
  have := ((tendsto_const_nhds (x := -eulerMascheroniConstant)).sub h1).add h2
  simp only [sub_zero, add_zero] at this
  refine this.congr fun s => ?_
  simp only [expIntegralOne]
  ring

/-- The Laplace transform `ω̂(s) = ∫_1^∞ e^{-su} ω(u) du`. -/
noncomputable def buchstabLaplace (s : ℝ) : ℝ := ∫ u in Ioi 1, exp (-(s * u)) * buchstab u

theorem integrableOn_exp_neg_mul {b : ℝ} (hb : 0 < b) (a : ℝ) :
    IntegrableOn (fun u => exp (-(b * u))) (Ioi a) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi a hb

theorem integrableOn_mul_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u => u * exp (-(b * u))) (Ioi 0) := by
  simpa [neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -1 < (1 : ℝ)) one_pos hb

theorem integrableOn_exp_mul_buchstab {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => exp (-(s * u)) * buchstab u) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_exp_neg_mul hs 1)
    (((by fun_prop : Measurable fun u : ℝ => exp (-(s * u))).mul
      measurable_buchstab).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
  rw [norm_mul, Real.norm_eq_abs, abs_exp]
  exact mul_le_of_le_one_right (exp_pos _).le (by simpa using abs_buchstab_le hu.le)

theorem integrableOn_mul_exp_mul_buchstab {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => u * exp (-(s * u)) * buchstab u) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_mul_exp_neg_mul hs).mono_set
    (Ioi_subset_Ioi zero_le_one))
    (((by fun_prop : Measurable fun u : ℝ => u * exp (-(s * u))).mul
      measurable_buchstab).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (by simpa using abs_buchstab_le hu.le)

/-- Differentiation under the integral sign: `ω̂'(s) = -∫_1^∞ u e^{-su} ω(u) du`. -/
theorem hasDerivAt_buchstabLaplace {s : ℝ} (hs : 0 < s) :
    HasDerivAt buchstabLaplace (-∫ u in Ioi 1, u * exp (-(s * u)) * buchstab u) s := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun u => exp (-(x * u)) * buchstab u)
      (volume.restrict (Ioi 1)) := fun x =>
    ((by fun_prop : Measurable fun u : ℝ => exp (-(x * u))).mul
      measurable_buchstab).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun x u => exp (-(x * u)) * buchstab u)
    (F' := fun x u => exp (-(x * u)) * (-u) * buchstab u) (x₀ := s)
    (bound := fun u => u * exp (-(s / 2 * u))) (Ioi_mem_nhds (half_lt_self hs))
    (Eventually.of_forall hmeas) (integrableOn_exp_mul_buchstab hs)
    (((by fun_prop : Measurable fun u : ℝ => exp (-(s * u)) * (-u)).mul
      measurable_buchstab).aestronglyMeasurable) ?_
    ((integrableOn_mul_exp_neg_mul (half_pos hs)).mono_set (Ioi_subset_Ioi zero_le_one)) ?_
  · have he : (∫ u in Ioi 1, exp (-(s * u)) * (-u) * buchstab u) =
        -∫ u in Ioi 1, u * exp (-(s * u)) * buchstab u := by
      rw [← integral_neg]
      congr 1
      ext u
      ring
    rw [← he]
    exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u) x (hx : s / 2 < x)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_exp,
      abs_neg, abs_of_pos (by linarith : 0 < u)]
    have h1 : exp (-(x * u)) ≤ exp (-(s / 2 * u)) := exp_le_exp.2 (by nlinarith)
    calc exp (-(x * u)) * u * |buchstab u| ≤ exp (-(s / 2 * u)) * u * 1 := by
          gcongr
          exact abs_buchstab_le hu.le
      _ = u * exp (-(s / 2 * u)) := by ring
  · filter_upwards with u x _
    have := (((hasDerivAt_id x).mul_const u).neg.exp).mul_const (buchstab u)
    convert this using 1 <;> simp

theorem setIntegral_Ioi_comp_sub (g : ℝ → ℝ) (a c : ℝ) :
    ∫ x in Ioi (a + c), g (x - c) = ∫ y in Ioi a, g y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  calc ∫ x, (Ioi (a + c)).indicator (fun x => g (x - c)) x
      = ∫ x, (Ioi a).indicator g (x - c) := by
        congr 1
        ext x
        simp only [indicator, mem_Ioi]
        split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
    _ = ∫ y, (Ioi a).indicator g y := integral_sub_right_eq_self _ c

/-- The Laplace transform of `u ω(u)`: `∫_1^∞ u e^{-su} ω(u) du = e^{-s} (1 + ω̂(s)) / s`
(integration by parts, using `(u ω(u))' = ω(u-1)`). -/
theorem integral_mul_exp_mul_buchstab {s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi 1, u * exp (-(s * u)) * buchstab u = exp (-s) * (1 + buchstabLaplace s) / s := by
  have hint := integrableOn_mul_exp_mul_buchstab hs
  have hs0 : s ≠ 0 := hs.ne'
  rw [← Ioc_union_Ioi_eq_Ioi (one_le_two : (1 : ℝ) ≤ 2),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi one_le_two))]
  -- the part over `(1, 2]`
  have h1 : ∫ u in Ioc 1 2, u * exp (-(s * u)) * buchstab u = (exp (-s) - exp (-(s * 2))) / s := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun u => exp (-(s * u))) fun u hu => by
      simp only
      rw [buchstab_of_le_two hu.2]
      field_simp [(show (0 : ℝ) < u by linarith [hu.1]).ne'],
      ← intervalIntegral.integral_of_le one_le_two]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -exp (-(s * u)) / s)
      (fun x _ => by
        have := ((((hasDerivAt_id x).const_mul s).neg).exp.neg).div_const s
        convert this using 1
        · funext y
          simp [neg_div]
        · simp only [Pi.neg_apply, id, mul_one]
          field_simp)
      ((by fun_prop : Continuous fun x : ℝ => exp (-(s * x))).intervalIntegrable 1 2)]
    simp only [mul_one]
    ring
  -- the part over `(2, ∞)`, by parts
  have hv : ∀ x, HasDerivAt (fun x => -exp (-(s * x)) / s) (exp (-(s * x))) x := fun x => by
    have := ((((hasDerivAt_id x).const_mul s).neg).exp.neg).div_const s
    convert this using 1
    · funext y
      simp [neg_div]
    · simp only [Pi.neg_apply, id, mul_one]
      field_simp
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul (a := 2) (u := fun x => x * buchstab x)
    (v := fun x => -exp (-(s * x)) / s) (u' := fun x => buchstab (x - 1))
    (v' := fun x => exp (-(s * x))) (a' := 2 * buchstab 2 * (-exp (-(s * 2)) / s)) (b' := 0)
    (fun x hx => hasDerivAt_mul_buchstab hx) (fun x _ => hv x)
    ((hint.mono_set (Ioi_subset_Ioi one_le_two)).congr_fun
      (fun x _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi) ?_ ?_ ?_
  rotate_left
  · refine Integrable.mono' ((integrableOn_exp_neg_mul hs 2).div_const s)
      (((measurable_buchstab.comp (measurable_sub_const 1)).mul
        (by fun_prop : Measurable fun x : ℝ => -exp (-(s * x)) / s)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 2 < x)
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_exp, abs_of_pos hs]
    exact mul_le_of_le_one_left (by positivity) (abs_buchstab_le (by linarith))
  · have hc : ContinuousAt (fun x => x * buchstab x * (-exp (-(s * x)) / s)) 2 :=
      (continuousAt_id.mul (continuousOn_buchstab.continuousAt (Ioi_mem_nhds two_pos))).mul
        ((by fun_prop : Continuous fun x : ℝ => -exp (-(s * x)) / s).continuousAt)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s hs).div_const s
    rw [zero_div] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Pi.mul_apply, rpow_one]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_neg, abs_exp, abs_of_pos hs, abs_of_pos (by linarith : (0 : ℝ) < x), neg_mul]
    have := abs_buchstab_le hx
    calc x * |buchstab x| * (exp (-(s * x)) / s) ≤ x * 1 * (exp (-(s * x)) / s) := by gcongr
      _ = x * exp (-(s * x)) / s := by ring
  have hshift : ∫ x in Ioi 2, buchstab (x - 1) * (-exp (-(s * x)) / s) =
      -(exp (-s) / s) * buchstabLaplace s := by
    calc ∫ x in Ioi 2, buchstab (x - 1) * (-exp (-(s * x)) / s)
        = ∫ x in Ioi (1 + 1), -(exp (-s) / s) *
            ((fun y => exp (-(s * y)) * buchstab y) (x - 1)) := by
          norm_num
          congr 1
          ext x
          rw [show exp (-(s * x)) = exp (-s) * exp (-(s * (x - 1))) by
            rw [← exp_add]; ring_nf]
          ring
      _ = -(exp (-s) / s) * ∫ x in Ioi (1 + 1), (fun y => exp (-(s * y)) * buchstab y) (x - 1) :=
          integral_const_mul _ _
      _ = -(exp (-s) / s) * buchstabLaplace s := by
          rw [setIntegral_Ioi_comp_sub (fun y => exp (-(s * y)) * buchstab y) 1 1]
          rfl
  rw [hshift, buchstab_of_le_two le_rfl] at hparts
  rw [h1, setIntegral_congr_fun measurableSet_Ioi (g := fun x => x * buchstab x * exp (-(s * x)))
    fun x _ => by ring, hparts]
  field_simp
  ring

theorem norm_buchstabLaplace_le {s : ℝ} (hs : 1 ≤ s) : ‖buchstabLaplace s‖ ≤ exp (-s) := by
  have hs0 : 0 < s := by linarith
  calc ‖buchstabLaplace s‖ ≤ ∫ u in Ioi 1, exp (-(s * u)) := by
        refine norm_integral_le_of_norm_le (integrableOn_exp_neg_mul hs0 1) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
        rw [norm_mul, Real.norm_eq_abs, abs_exp]
        exact mul_le_of_le_one_right (exp_pos _).le (by simpa using abs_buchstab_le hu.le)
    _ = exp (-s) / s := by
        simp_rw [← neg_mul]
        rw [integral_exp_mul_Ioi (by linarith) 1]
        field_simp
    _ ≤ exp (-s) := div_le_self (exp_pos _).le hs

/-- The Laplace transform of Buchstab's function: `1 + ω̂(s) = exp(E₁(s))` for `s > 0`. -/
theorem one_add_buchstabLaplace {s : ℝ} (hs : 0 < s) :
    1 + buchstabLaplace s = exp (expIntegralOne s) := by
  set Φ : ℝ → ℝ := fun t => (1 + buchstabLaplace t) * exp (-expIntegralOne t)
  have hΦ : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt Φ 0 t := by
    intro t ht
    have ht : 0 < t := ht
    have h1 := (hasDerivAt_buchstabLaplace ht).const_add 1
    have h2 := (hasDerivAt_expIntegralOne ht).neg.exp
    convert h1.mul h2 using 1
    rw [integral_mul_exp_mul_buchstab ht]
    field_simp
    ring
  have hconst : ∀ t ∈ Ioi (0 : ℝ), Φ t = Φ s := fun t ht =>
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
      (fun x hx => (hΦ x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hΦ x hx).deriv) ht hs
  have hlim : Tendsto Φ atTop (𝓝 1) := by
    have hL : Tendsto buchstabLaplace atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ tendsto_exp_neg_atTop_nhds_zero
      filter_upwards [eventually_ge_atTop 1] with t ht
      exact norm_buchstabLaplace_le ht
    have := (hL.const_add 1).mul (tendsto_expIntegralOne_atTop.neg.rexp)
    simpa using this
  have hΦs : Φ s = 1 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (hconst t ht).symm
  simp only [Φ] at hΦs
  rwa [exp_neg, mul_inv_eq_one₀ (exp_pos _).ne'] at hΦs

/-- de Bruijn's theorem, in Laplace form: if `ω - c` is integrable on `(1, ∞)` (for instance if
`ω(u) = c + O(e^{-u})`), then `c = e^{-γ}`. -/
theorem eq_exp_neg_of_integrableOn_buchstab_sub {c : ℝ}
    (hc : IntegrableOn (fun u => buchstab u - c) (Ioi 1)) :
    c = exp (-eulerMascheroniConstant) := by
  set I := ∫ u in Ioi 1, ‖buchstab u - c‖
  have hX : ∀ s > 0, s * buchstabLaplace s =
      s * (∫ u in Ioi 1, exp (-(s * u)) * (buchstab u - c)) + c * exp (-s) := by
    intro s hs
    have hi1 : IntegrableOn (fun u => exp (-(s * u)) * (buchstab u - c)) (Ioi 1) := by
      refine Integrable.mono' hc.norm
        (((by fun_prop : Measurable fun u : ℝ => exp (-(s * u))).mul
          (measurable_buchstab.sub_const c)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
      rw [norm_mul, Real.norm_eq_abs, abs_exp]
      exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.2 (by nlinarith))
    have hi2 : IntegrableOn (fun u => exp (-(s * u)) * c) (Ioi 1) :=
      (integrableOn_exp_neg_mul hs 1).mul_const c
    have hsplit : buchstabLaplace s = (∫ u in Ioi 1, exp (-(s * u)) * (buchstab u - c)) +
        ∫ u in Ioi 1, exp (-(s * u)) * c := by
      rw [← integral_add hi1 hi2, buchstabLaplace]
      congr 1
      ext u
      ring
    rw [hsplit, integral_mul_const]
    simp_rw [← neg_mul]
    rw [integral_exp_mul_Ioi (by linarith) 1]
    field_simp
  have hb : ∀ s > 0, ‖∫ u in Ioi 1, exp (-(s * u)) * (buchstab u - c)‖ ≤ I := by
    intro s hs
    refine norm_integral_le_of_norm_le hc.norm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
    rw [norm_mul, Real.norm_eq_abs, abs_exp]
    exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.2 (by nlinarith))
  have h1 : Tendsto (fun s => s * buchstabLaplace s) (𝓝[>] 0) (𝓝 c) := by
    have hs0 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hA : Tendsto (fun s => s * (∫ u in Ioi 1, exp (-(s * u)) * (buchstab u - c)))
        (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using hs0.mul_const I)
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left (hb s hs) hs.le
    have hB : Tendsto (fun s => c * exp (-s)) (𝓝[>] 0) (𝓝 c) := by
      simpa using ((continuous_exp.comp continuous_neg).tendsto 0).mono_left
        nhdsWithin_le_nhds |>.const_mul c
    refine (by simpa using hA.add hB : Tendsto _ _ (𝓝 c)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact (hX s hs).symm
  have h2 : Tendsto (fun s => s * buchstabLaplace s) (𝓝[>] 0)
      (𝓝 (exp (-eulerMascheroniConstant))) := by
    have hs0 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    refine (by simpa using tendsto_expIntegralOne_add_log.rexp.sub hs0 :
      Tendsto _ _ (𝓝 (exp (-eulerMascheroniConstant)))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    rw [exp_add, exp_log hs, ← one_add_buchstabLaplace hs]
    ring
  exact tendsto_nhds_unique h1 h2

end IwaniecLinearSieve
