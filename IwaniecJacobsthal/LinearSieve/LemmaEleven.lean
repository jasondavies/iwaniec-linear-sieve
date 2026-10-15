import IwaniecJacobsthal.LinearSieve.LemmaSeven

/-!
# [I71, Lemmas 11 and 12]

Write `L = log y`, `x(t) = t² log⁵ t / L²`, `w(t) = t² log⁴ t / L²` and
`A_a(t) = (1 + x(t))^{5(t - a)}` (so `δ(t, y) = A_0(t)`). The logarithmic derivative of `A_a` is
`E_a(t) = 5 log (1 + x) + 5 (t - a) x'/(1 + x) ≤ w (15 log t + 25)` (`rate_bound`).
With the Corollary to Lemma 10 (`c₃ = 4`), `G_{r+1}(t) log t < 4 G_r(t-1) t/(t-1)²`, this gives,
for `log t ≥ 32` and `160 w(t) ≤ 1`:

* `lemma11`: `∫_s^b A_1(t) G_r(t-1) t/(t-1)² dt < δ(s) G_{r+1}(s)` for `e^{32} ≤ s ≤ b` with
  `160 b² log⁴ b ≤ L²` ([I71, (3.15)]; [I71] has `s₀ = e^{(120 c₃)^{5/2}}` and the
  condition `100 c₃ ξ² log⁴ ξ < L²`);
* `lemma12`: `A_1(t) G_{r+1}(t)` is antitone on `[s, b]`;
* `antitoneOn_cor3Weight`: `A_1(t) G_r(t-1) t²/(t-1)²` is antitone on `[s, b]` (this is the
  monotonicity of `b(x)` in the proof of [I71, Corollary 3]; [I71] refers to Lemma 12 for it).

Finally `exists_xi_large`: for large `y`, `ξ(y) ≥ e^{32}`, `160 ξ² log⁴ ξ ≤ L²` and `y^{1/ξ} ≥ 2`,
via `xi_sq_mul_log_pow_four_div_le : ξ² log⁴ ξ / L² ≤ (log log 3y)^{-2/5}`.
-/

open Real Set Filter Topology MeasureTheory

namespace IwaniecJacobsthal

/-! ### The growth factor `(1 + t² log⁵ t / L²)^{5(t-a)}` -/

theorem hasDerivAt_lsx (L : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ 2 * log t ^ 5 / L ^ 2)
      ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) t := by
  have h := ((hasDerivAt_pow 2 t).mul ((hasDerivAt_log ht.ne').pow 5)).div_const (L ^ 2)
  simp only [Pi.pow_apply, Pi.mul_apply] at h
  convert h using 1
  field_simp
  ring

theorem lsx_nonneg (L : ℝ) {t : ℝ} (ht : 1 ≤ t) : 0 ≤ t ^ 2 * log t ^ 5 / L ^ 2 := by
  have := log_nonneg ht
  positivity

theorem hasDerivAt_growth (L a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a)))
      ((1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a)) *
        (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
          ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
            (1 + t ^ 2 * log t ^ 5 / L ^ 2))) t := by
  set x := t ^ 2 * log t ^ 5 / L ^ 2
  have hx : 0 < 1 + x := by linarith [lsx_nonneg L ht]
  have h := ((hasDerivAt_lsx L (by linarith)).const_add 1).rpow
    (((hasDerivAt_id' t).sub_const a).const_mul 5) hx
  convert h using 1
  rw [rpow_sub_one hx.ne']
  field_simp
  ring

/-- The logarithmic derivative of `(1 + x)^{5(t-a)}` is at most `w (15 log t + 25)`; the
consequences used below. -/
theorem rate_bound {L a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht1 : 1 ≤ t) (ht : 32 ≤ log t)
    (hw : t ^ 2 * log t ^ 4 / L ^ 2 ≤ 1 / 160) :
    0 ≤ 5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2) ∧
    4 * (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2))
      ≤ log t - 1 ∧
    4 * (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2)) *
        (1 + 5 * (t ^ 2 * log t ^ 5 / L ^ 2)) ≤ 5 * (t ^ 2 * log t ^ 5 / L ^ 2) * log t := by
  set u := log t with hu
  set W := t ^ 2 * u ^ 4 / L ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hx : t ^ 2 * u ^ 5 / L ^ 2 = W * u := by rw [hW]; ring
  have hx' : t * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) = W * (2 * u + 5) := by rw [hW]; ring
  have hd0 : 0 ≤ (2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2 := by
    have : 0 ≤ u := by linarith
    positivity
  rw [hx]
  set E := 5 * log (1 + W * u) + 5 * (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) /
    (1 + W * u) with hE
  have hWu : 0 ≤ W * u := mul_nonneg hW0 (by linarith)
  have h1 : 0 ≤ log (1 + W * u) := log_nonneg (by linarith)
  have h2 : log (1 + W * u) ≤ W * u := by
    have := log_le_sub_one_of_pos (by linarith : 0 < 1 + W * u); linarith
  have h3 : 0 ≤ (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) / (1 + W * u) :=
    div_nonneg (mul_nonneg (by linarith) hd0) (by linarith)
  have h4 : (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) / (1 + W * u) ≤
      W * (2 * u + 5) := by
    rw [div_le_iff₀ (by linarith), ← hx']
    have : (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) ≤
        t * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hd0
    nlinarith [mul_nonneg hWu (mul_nonneg (by linarith : (0 : ℝ) ≤ t) hd0)]
  have hE0 : 0 ≤ E := by rw [hE, mul_assoc 5, mul_div_assoc]; positivity
  have hE1 : 4 * E ≤ W * (60 * u + 100) := by
    rw [hE, mul_assoc 5 (t - a), mul_div_assoc]; nlinarith
  refine ⟨hE0, by nlinarith, ?_⟩
  have hu0 : 0 < u := by linarith
  calc 4 * E * (1 + 5 * (W * u)) ≤ W * (60 * u + 100) * (1 + 5 * (W * u)) := by
        gcongr
    _ ≤ 5 * (W * u) * u := by
        have : W * (W * u) ≤ W * (u / 160) := mul_le_mul_of_nonneg_left (by nlinarith) hW0
        nlinarith [mul_nonneg hW0 hu0.le]

/-! ### The Corollary to Lemma 10 in the form used here -/

theorem majG_succ_mul_log_lt (r : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    majG (r + 1) t * log t < 4 * (majG r (t - 1) * t / (t - 1) ^ 2) := by
  have h := majG_succ_mul_log_div_lt r ht
  have hK : 0 < majG r (t - 1) * t := mul_pos (majG_pos r _) (by linarith)
  have h1 : 0 < (t - 1) ^ 2 := by nlinarith
  rw [div_lt_iff₀ hK] at h
  rw [mul_div_assoc', lt_div_iff₀ h1]
  linarith

theorem five_add_neg_one_pow_div_le (r : ℕ) : (5 + (-1 : ℝ) ^ r) / 2 ≤ 3 := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_one_pow]; norm_num
  · rw [hr.neg_one_pow]; norm_num

/-! ### The range `e^{32} ≤ t ≤ b`, `160 b² log⁴ b ≤ L²` -/

/-- On `[e^{32}, b]` with `160 b² log⁴ b ≤ L²`: `1 ≤ t`, `32 ≤ log t` and `160 w(t) ≤ 1`. -/
theorem range_facts {L t b : ℝ} (ht : exp 32 ≤ t) (htb : t ≤ b)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) :
    1 ≤ t ∧ 32 ≤ log t ∧ t ^ 2 * log t ^ 4 / L ^ 2 ≤ 1 / 160 ∧ 0 < L ^ 2 := by
  have ht1 : 1 ≤ t := le_trans (by linarith [add_one_le_exp (32 : ℝ)]) ht
  have hlt : 32 ≤ log t := (le_log_iff_exp_le (by linarith)).2 ht
  have hlb : log t ≤ log b := log_le_log (by linarith) htb
  have h4 : t ^ 2 * log t ^ 4 ≤ b ^ 2 * log b ^ 4 := by
    have : 0 ≤ log t := by linarith
    gcongr
  have hpos : 0 < t ^ 2 * log t ^ 4 := by
    have : 0 < log t := by linarith
    have : 0 < t := by linarith
    positivity
  have hL : 0 < L ^ 2 := by linarith
  refine ⟨ht1, hlt, ?_, hL⟩
  rw [div_le_iff₀ hL]; linarith

/-- `(1 + x)^{5(t-1)} = (1 + x)^{5t} / (1 + x)^5`. -/
theorem rpow_five_mul_sub_one {x : ℝ} (hx : 0 < x) (t : ℝ) :
    x ^ (5 * (t - 1)) = x ^ (5 * t) / x ^ 5 := by
  rw [show 5 * (t - 1) = 5 * t - 5 by ring, rpow_sub hx]
  norm_cast

theorem continuousAt_growth (L a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ContinuousAt (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a))) t :=
  (hasDerivAt_growth L a ht).continuousAt

theorem continuousOn_lemma11_integrand (L : ℝ) (r : ℕ) {s b : ℝ} (hs : 2 ≤ s) :
    ContinuousOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2) (Icc s b) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
  exact (((continuousAt_growth L 1 (by linarith [ht.1])).mul
    ((continuous_majG r).continuousAt.comp (continuous_sub_right 1).continuousAt)).mul
    continuousAt_id).div ((continuous_sub_right 1).continuousAt.pow 2) (pow_ne_zero 2 ht1)

theorem delta_eq_growth (s y : ℝ) :
    delta s y = (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * (s - 0)) := by
  rw [delta, sub_zero]

theorem delta_pos {s : ℝ} (hs : 1 ≤ s) (y : ℝ) : 0 < delta s y := by
  have := lsx_nonneg (log y) hs
  exact rpow_pos_of_pos (by linarith) _

/-- [I71, Lemma 11] ((3.15)), with `s₀ = e^{32}`, `c₃ = 4`, and the upper limit `ξ` replaced by any
`b` with `160 b² log⁴ b ≤ log² y`:
`∫_s^b (1 + t² log⁵ t / L²)^{5(t-1)} G_r(t-1) t/(t-1)² dt < δ(s, y) G_{r+1}(s)`. -/
theorem lemma11 (r : ℕ) {y s b : ℝ} (hs : exp 32 ≤ s) (hsb : s ≤ b)
    (hb : b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160) :
    ∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2 < delta s y * majG (r + 1) s := by
  set L := log y
  have hs1 : 1 ≤ s := (range_facts hs hsb hb).1
  have hs3 : 3 < s := by linarith [add_one_le_exp (32 : ℝ)]
  -- `τ(t) = δ(t) G_{r+1}(t)` and its derivative
  set τ : ℝ → ℝ := fun t => delta t y * majG (r + 1) t with hτ
  have hτd : ∀ t, 3 < t → HasDerivAt τ
      ((1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 0)) *
        (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - 0) *
          ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
            (1 + t ^ 2 * log t ^ 5 / L ^ 2)) * majG (r + 1) t +
        (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 0)) *
          (-(majG r (t - 1) * t / (t - 1) ^ 2))) t := fun t ht => by
    have h1 := hasDerivAt_growth L 0 (t := t) (by linarith)
    have h2 := hasDerivAt_majG_succ r (t := t) (by linarith [five_add_neg_one_pow_div_le r])
    have := h1.mul h2
    simp only [τ, delta_eq_growth]
    exact this
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (g := fun t => -τ t)
    (φ := fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2) hsb
    (continuousOn_of_forall_continuousAt fun t ht => (hτd t (by linarith [ht.1])).continuousAt.neg)
    (fun t ht => (hτd t (by linarith [ht.1])).neg.hasDerivWithinAt)
    ((continuousOn_lemma11_integrand L r (by linarith)).integrableOn_Icc) ?_
  · have hτb : 0 < τ b := mul_pos (delta_pos (by linarith) y) (majG_pos _ _)
    simp only [τ] at key hτb ⊢
    linarith
  -- the pointwise inequality `-τ' ≥ (1 + x)^{5(t-1)} G_r(t-1) t/(t-1)²`
  intro t ht
  have ht3 : 3 < t := by linarith [ht.1]
  obtain ⟨ht1, hlt, hw, hL⟩ := range_facts (L := L) (hs.trans ht.1.le) ht.2.le hb
  obtain ⟨hE0, -, hE2⟩ := rate_bound (L := L) (a := 0) le_rfl zero_le_one ht1 hlt hw
  set x := t ^ 2 * log t ^ 5 / L ^ 2 with hx
  set E := 5 * log (1 + x) + 5 * (t - 0) * ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
    (1 + x) with hE
  have hK0 : 0 < majG r (t - 1) * t / (t - 1) ^ 2 := by
    have : 0 < t - 1 := by linarith
    have := majG_pos r (t - 1)
    have : 0 < t := by linarith
    positivity
  set K := majG r (t - 1) * t / (t - 1) ^ 2 with hK
  set G := majG (r + 1) t
  have hx0 : 0 ≤ x := lsx_nonneg L ht1
  have hG : G * log t < 4 * K := majG_succ_mul_log_lt r (by linarith)
  have hP : 0 < (1 + x) ^ (5 * (t - 0)) := rpow_pos_of_pos (by linarith) _
  have hbern : 1 + 5 * x ≤ (1 + x) ^ 5 := by
    have := one_add_mul_le_pow (a := x) (by linarith) 5
    norm_num at this ⊢; linarith
  -- `E G (1 + 5x) ≤ 5 x K`
  have i1 : E * (G * log t) ≤ E * (4 * K) := mul_le_mul_of_nonneg_left hG.le hE0
  have i2 : 4 * E * (1 + 5 * x) * K ≤ 5 * x * log t * K := mul_le_mul_of_nonneg_right hE2 hK0.le
  have i3 : E * G * (1 + 5 * x) ≤ 5 * x * K := by
    have hl : 0 < log t := by linarith
    have : log t * (E * G * (1 + 5 * x)) ≤ log t * (5 * x * K) := by nlinarith
    exact le_of_mul_le_mul_left this hl
  have i4 : K / (1 + x) ^ 5 ≤ K - E * G := by
    calc K / (1 + x) ^ 5 ≤ K / (1 + 5 * x) :=
          div_le_div_of_nonneg_left hK0.le (by linarith) hbern
      _ ≤ K - E * G := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
  show (1 + x) ^ (5 * (t - 1)) * majG r (t - 1) * t / (t - 1) ^ 2 ≤
    -((1 + x) ^ (5 * (t - 0)) * E * G + (1 + x) ^ (5 * (t - 0)) * -K)
  rw [rpow_five_mul_sub_one (by linarith)]
  simp only [sub_zero] at hP ⊢
  calc (1 + x) ^ (5 * t) / (1 + x) ^ 5 * majG r (t - 1) * t / (t - 1) ^ 2
      = (1 + x) ^ (5 * t) * (K / (1 + x) ^ 5) := by rw [hK]; ring
    _ ≤ (1 + x) ^ (5 * t) * (K - E * G) := mul_le_mul_of_nonneg_left i4 hP.le
    _ = _ := by ring

/-! ### Lemma 12 and the monotonicity used in Corollary 3 -/

theorem four_lt_of_exp_le {t : ℝ} (ht : exp 32 ≤ t) : 4 < t := by
  linarith [add_one_le_exp (32 : ℝ)]

/-- If `g ≥ 0` has derivative `-k` with `g ℓ ≤ 4 k` and `ℓ ≥ log t - 1`, then
`(1 + x)^{5(t-1)} g(t)` is antitone on `[s, b]` (for `e^{32} ≤ s`, `160 b² log⁴ b ≤ L²`). -/
theorem antitoneOn_growth_mul {L s b : ℝ} {g k ℓ : ℝ → ℝ} (hs : exp 32 ≤ s)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) (hg : ∀ t ∈ Icc s b, HasDerivAt g (-k t) t)
    (hg0 : ∀ t ∈ Icc s b, 0 ≤ g t) (hgk : ∀ t ∈ Icc s b, g t * ℓ t ≤ 4 * k t)
    (hℓ : ∀ t ∈ Icc s b, log t - 1 ≤ ℓ t) :
    AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * g t) (Icc s b) := by
  have hd : ∀ t ∈ Icc s b, HasDerivAt
      (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * g t)
      ((1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) *
        (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - 1) *
          ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
            (1 + t ^ 2 * log t ^ 5 / L ^ 2)) * g t +
        (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * -k t) t := fun t ht =>
    (hasDerivAt_growth L 1 (range_facts (hs.trans ht.1) ht.2 hb).1).mul (hg t ht)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s b)
    (continuousOn_of_forall_continuousAt fun t ht => (hd t ht).continuousAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) fun t ht => ?_
  have ht' := interior_subset ht
  obtain ⟨ht1, hlt, hw, -⟩ := range_facts (hs.trans ht'.1) ht'.2 hb
  obtain ⟨hE0, hE1, -⟩ := rate_bound (L := L) (a := 1) zero_le_one le_rfl ht1 hlt hw
  set E := 5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - 1) *
    ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2)
  have hP : 0 < (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) :=
    rpow_pos_of_pos (by linarith [lsx_nonneg L ht1]) _
  have hℓ' := hℓ t ht'
  have hgk' := hgk t ht'
  have hg0' := hg0 t ht'
  have hℓ0 : 0 < ℓ t := by linarith
  have hk0 : 0 ≤ k t := by nlinarith
  have h1 : ℓ t * (E * g t) ≤ ℓ t * k t := by nlinarith
  have h2 : E * g t ≤ k t := le_of_mul_le_mul_left h1 hℓ0
  nlinarith

/-- [I71, Lemma 12]: `μ(t) = (1 + t² log⁵ t / L²)^{5(t-1)} G_{r+1}(t)` is antitone on `[s, b]`
for `e^{32} ≤ s` and `160 b² log⁴ b ≤ L²`. -/
theorem lemma12 (r : ℕ) {L s b : ℝ} (hs : exp 32 ≤ s) (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) :
    AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG (r + 1) t)
      (Icc s b) := by
  refine antitoneOn_growth_mul (k := fun t => majG r (t - 1) * t / (t - 1) ^ 2) (ℓ := log) hs hb
    (fun t ht => ?_) (fun t _ => (majG_pos _ _).le) (fun t ht => ?_) fun t _ => by linarith
  · exact hasDerivAt_majG_succ r (by
      linarith [five_add_neg_one_pow_div_le r, four_lt_of_exp_le (hs.trans ht.1)])
  · exact (majG_succ_mul_log_lt r (by linarith [four_lt_of_exp_le (hs.trans ht.1)])).le

theorem log_sub_one_ge {t : ℝ} (ht : 2 ≤ t) : log t - 1 ≤ log (t - 1) := by
  have h1 : 0 < t - 1 := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < t) h1)
  rw [log_div (by linarith) h1.ne'] at h
  have : t / (t - 1) - 1 ≤ 1 := by
    rw [div_sub_one h1.ne', div_le_one h1]; linarith
  linarith

theorem antitoneOn_sq_div_sq_sub_one : AntitoneOn (fun t : ℝ => t ^ 2 / (t - 1) ^ 2) (Ioi 1) := by
  intro u hu v hv huv
  have hu1 : 0 < u - 1 := by linarith [hu.out]
  have hv1 : 0 < v - 1 := by linarith [hv.out]
  have h : v / (v - 1) ≤ u / (u - 1) := by
    rw [div_le_div_iff₀ hv1 hu1]; nlinarith
  have h0 : 0 ≤ v / (v - 1) := div_nonneg (by linarith) hv1.le
  simp only
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_left₀ h0 h 2

theorem antitoneOn_mul_of_nonneg {f g : ℝ → ℝ} {S : Set ℝ} (hf : AntitoneOn f S)
    (hg : AntitoneOn g S) (hf0 : ∀ t ∈ S, 0 ≤ f t) (hg0 : ∀ t ∈ S, 0 ≤ g t) :
    AntitoneOn (fun t => f t * g t) S := fun u hu v hv huv =>
  mul_le_mul (hf hu hv huv) (hg hu hv huv) (hg0 v hv) (hf0 u hu)

/-- The weight in the proof of [I71, Corollary 3]:
`(1 + t² log⁵ t / L²)^{5(t-1)} G_r(t-1) t²/(t-1)²` is antitone on `[s, b]`. -/
theorem antitoneOn_cor3Weight (r : ℕ) {L s b : ℝ} (hs : exp 32 ≤ s)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) :
    AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) *
      (t ^ 2 / (t - 1) ^ 2)) (Icc s b) := by
  have hfacts : ∀ t ∈ Icc s b, 4 < t := fun t ht => four_lt_of_exp_le (hs.trans ht.1)
  have hψ : AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) *
      majG r (t - 1)) (Icc s b) := by
    refine antitoneOn_growth_mul
      (k := fun t => majG (r + 1) (t - 1 - 1) * (t - 1) / (t - 1 - 1) ^ 2)
      (ℓ := fun t => log (t - 1)) hs hb (fun t ht => ?_) (fun t _ => (majG_pos _ _).le)
      (fun t ht => ?_) fun t ht => log_sub_one_ge (by linarith [hfacts t ht])
    · have h := hasDerivAt_majG_succ (r + 1) (t := t - 1)
        (by linarith [five_add_neg_one_pow_div_le (r + 1), hfacts t ht])
      rw [majG_add_two] at h
      exact h.comp_sub_const t 1
    · have h := majG_succ_mul_log_lt (r + 1) (t := t - 1) (by linarith [hfacts t ht])
      rw [majG_add_two] at h
      exact h.le
  refine antitoneOn_mul_of_nonneg hψ
    (antitoneOn_sq_div_sq_sub_one.mono fun t ht => show (1 : ℝ) < t by linarith [hfacts t ht])
    (fun t ht => ?_) fun t _ => by positivity
  have := lsx_nonneg L (by linarith [hfacts t ht] : (1 : ℝ) ≤ t)
  exact mul_nonneg (rpow_pos_of_pos (by linarith) _).le (majG_pos _ _).le

/-! ### The size of `ξ` -/

/-- `ξ² log⁴ ξ / L² ≤ (log log 3y)^{-2/5}` (cf. [I71, proof of Lemma 11]). -/
theorem xi_sq_mul_log_pow_four_div_le {y : ℝ} (hy : 1 < y) (hℓ : 1 ≤ log (log (3 * y)))
    (hξ : 1 ≤ xi y) :
    xi y ^ 2 * log (xi y) ^ 4 / log y ^ 2 ≤ log (log (3 * y)) ^ (-(2 / 5 : ℝ)) := by
  set ℓ := log (log (3 * y)) with hℓdef
  set L := log y with hL
  have hL0 : 0 < L := log_pos hy
  have hℓ0 : 0 < ℓ := by linarith
  have hP : 1 ≤ ℓ ^ (11 / 5 : ℝ) := one_le_rpow hℓ (by norm_num)
  have hξL : xi y ≤ L := by
    rw [xi]; exact div_le_self hL0.le hP
  have h3 : L ≤ log (3 * y) := by
    rw [log_mul (by norm_num) (by linarith)]; linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hlogξ : log (xi y) ≤ ℓ := log_le_log (by linarith) (by linarith)
  have hlogξ0 : 0 ≤ log (xi y) := log_nonneg hξ
  have hsq : xi y ^ 2 / L ^ 2 = (ℓ ^ (22 / 5 : ℝ))⁻¹ := by
    have hx : xi y = L / ℓ ^ (11 / 5 : ℝ) := rfl
    have h2 : (ℓ ^ (11 / 5 : ℝ)) ^ 2 = ℓ ^ (22 / 5 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hℓ0.le]; norm_num
    rw [hx, div_pow, h2]
    field_simp
  have hP' : 0 < ℓ ^ (22 / 5 : ℝ) := rpow_pos_of_pos hℓ0 _
  calc xi y ^ 2 * log (xi y) ^ 4 / L ^ 2 = log (xi y) ^ 4 * (xi y ^ 2 / L ^ 2) := by ring
    _ ≤ ℓ ^ 4 * (ℓ ^ (22 / 5 : ℝ))⁻¹ := by
        rw [hsq]; gcongr
    _ = ℓ ^ (-(2 / 5 : ℝ)) := by
        rw [← rpow_natCast, ← rpow_neg hℓ0.le, ← rpow_add hℓ0]; norm_num

theorem tendsto_log_log_three_mul : Tendsto (fun y : ℝ => log (log (3 * y))) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num)))

/-- `ξ(y) → ∞`. -/
theorem tendsto_xi : Tendsto xi atTop atTop := by
  have hv : Tendsto (fun y : ℝ => log (3 * y)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have ho := (isLittleO_log_rpow_rpow_atTop (11 / 5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hbound : ∀ᶠ y in atTop, log (3 * y) ^ (1 / 2 : ℝ) / 2 ≤ xi y := by
    filter_upwards [hv.eventually ho, hv.eventually (eventually_ge_atTop (exp 1)),
      hv.eventually (eventually_ge_atTop (2 * log 3)), eventually_gt_atTop 1] with y h1 h2 h3 hy
    simp only [one_mul] at h1 h2 h3
    have hv0 : 0 < log (3 * y) := by linarith [exp_pos 1]
    have hℓ : 1 ≤ log (log (3 * y)) := (le_log_iff_exp_le hv0).2 h2
    rw [norm_of_nonneg (rpow_nonneg (by linarith) _),
      norm_of_nonneg (rpow_nonneg hv0.le _)] at h1
    have hL : log y = log (3 * y) - log 3 := by
      rw [log_mul (by norm_num) (by linarith)]; ring
    have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos (by linarith) _
    have hsq : 0 < log (3 * y) ^ (1 / 2 : ℝ) := rpow_pos_of_pos hv0 _
    have hsq2 : log (3 * y) ^ (1 / 2 : ℝ) * log (3 * y) ^ (1 / 2 : ℝ) = log (3 * y) := by
      rw [← rpow_add hv0]; norm_num
    rw [xi, hL, le_div_iff₀ hP]
    calc log (3 * y) ^ (1 / 2 : ℝ) / 2 * log (log (3 * y)) ^ (11 / 5 : ℝ)
        ≤ log (3 * y) ^ (1 / 2 : ℝ) / 2 * log (3 * y) ^ (1 / 2 : ℝ) := by gcongr
      _ = log (3 * y) / 2 := by rw [div_mul_eq_mul_div, hsq2]
      _ ≤ log (3 * y) - log 3 := by linarith
  exact tendsto_atTop_mono' atTop hbound
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hv).atTop_div_const (by norm_num))

/-- For `y` large: `ξ(y) ≥ e^{32}`, `160 ξ² log⁴ ξ ≤ log² y` and `y^{1/ξ} ≥ 2`, so that Lemmas 11, 12
and Corollary 3 apply up to `b = ξ(y)`. -/
theorem exists_xi_large : ∃ y₀ : ℝ, ∀ y ≥ y₀, 1 < y ∧ exp 32 ≤ xi y ∧
    xi y ^ 2 * log (xi y) ^ 4 ≤ log y ^ 2 / 160 ∧ 2 ≤ y ^ (1 / xi y) := by
  have hsmall : ∀ᶠ y in atTop, log (log (3 * y)) ^ (-(2 / 5 : ℝ)) ≤ 1 / 160 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_log_log_three_mul).eventually (eventually_le_nhds (by norm_num))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 (hsmall.and ((tendsto_xi.eventually
    (eventually_ge_atTop (exp 32))).and ((tendsto_log_log_three_mul.eventually
      (eventually_ge_atTop 1)).and (eventually_gt_atTop 1))))
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy₀ y hy
  have hξ1 : 1 ≤ xi y := le_trans (by linarith [add_one_le_exp (32 : ℝ)]) h2
  have hL0 : 0 < log y := log_pos h4
  refine ⟨h4, h2, ?_, ?_⟩
  · have := (xi_sq_mul_log_pow_four_div_le h4 h3 hξ1).trans h1
    rwa [div_le_iff₀ (by positivity), div_mul_eq_mul_div, one_mul] at this
  · have hℓ0 : 0 < log (log (3 * y)) := by linarith
    have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ0 _
    rw [rpow_def_of_pos (by linarith), xi, mul_one_div, div_div_cancel₀ hL0.ne']
    have : 1 ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) := one_le_rpow h3 (by norm_num)
    calc (2 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
      _ ≤ _ := exp_le_exp.2 this

end IwaniecJacobsthal
