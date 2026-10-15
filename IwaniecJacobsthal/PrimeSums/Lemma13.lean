import IwaniecJacobsthal.PrimeSums.Mertens
import IwaniecJacobsthal.PrimeSums.SummationByParts

/-!
# [I71, Lemma 13] and [I71, Lemma 14]

For `b ≥ 0` monotone on `[B, A]`, `2 ≤ B ≤ A`,
`∑_{B ≤ p ≤ A} b(p)/p = ∫_B^A b(x) / (x log x) dx + O(b(A) exp(-κ √(log B)))`,
and the analogous statement with `b(B)` for `b` antitone.

The proof is Iwaniec's: summation by parts against `S(n)` (in the abstract form
`abs_sum_sub_integral_le`) at the points `B, ⌊B⌋ + 1, …, ⌊A⌋, A`, using `S_asymp`.
-/

open Real Finset MeasureTheory intervalIntegral

namespace IwaniecJacobsthal

/-! ### Elementary facts about `log ∘ log` -/

theorem continuousOn_inv_mul_log {u v : ℝ} (hu : 1 < u) :
    ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.Icc u v) := by
  have hpos : ∀ x ∈ Set.Icc u v, 1 < x := fun x hx ↦ by linarith [hx.1]
  refine ContinuousOn.inv₀ (ContinuousOn.mul continuousOn_id ?_) fun x hx ↦ ?_
  · exact continuousOn_log.mono fun x hx ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos x hx]
  · have := hpos x hx
    have := log_pos this
    positivity

theorem integral_inv_mul_log {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    ∫ x in u..v, (x * log x)⁻¹ = log (log v) - log (log u) := by
  have hpos : ∀ x ∈ Set.uIcc u v, 1 < x := fun x hx ↦ by
    rw [Set.uIcc_of_le huv] at hx; linarith [hx.1]
  refine integral_eq_sub_of_hasDerivAt (f := fun x ↦ log (log x)) (fun x hx ↦ ?_) ?_
  · have hx := hpos x hx
    have h := (hasDerivAt_log (by linarith : x ≠ 0)).log (log_pos hx).ne'
    convert h using 1
    rw [mul_inv, div_eq_mul_inv]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    exact continuousOn_inv_mul_log hu

theorem log_log_sub_log_log_le {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    log (log v) - log (log u) ≤ (v - u) / (u * log u) := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < log u := log_pos hu
  have hlv : 0 < log v := log_pos (by linarith)
  have h1 : log (log v) - log (log u) ≤ log v / log u - 1 := by
    rw [← log_div hlv.ne' hlu.ne']
    exact log_le_sub_one_of_pos (div_pos hlv hlu)
  have h2 : log v - log u ≤ v / u - 1 := by
    rw [← log_div (by linarith) hu0.ne']
    exact log_le_sub_one_of_pos (div_pos (by linarith) hu0)
  calc log (log v) - log (log u) ≤ log v / log u - 1 := h1
    _ = (log v - log u) / log u := by field_simp
    _ ≤ (v / u - 1) / log u := by gcongr
    _ = (v - u) / (u * log u) := by field_simp

/-! ### The partition `B, ⌊B⌋ + 1, …, ⌊A⌋, A` of `[B, A]` -/

/-- The points `B = a 0 ≤ ⌊B⌋ + 1 ≤ ⋯ ≤ ⌊A⌋ ≤ A = a (⌊A⌋ - ⌊B⌋ + 1)`. -/
noncomputable def clampPt (B A : ℝ) (j : ℕ) : ℝ := max B (min ((⌊B⌋₊ + j : ℕ) : ℝ) A)

theorem clampPt_mono (B A : ℝ) : Monotone (clampPt B A) := fun i j hij ↦ by
  unfold clampPt
  gcongr

theorem clampPt_zero {B A : ℝ} (hB : 0 ≤ B) : clampPt B A 0 = B := by
  unfold clampPt
  exact max_eq_left ((min_le_left _ _).trans (by simpa using Nat.floor_le hB))

theorem clampPt_last {B A : ℝ} (hBA : B ≤ A) :
    clampPt B A (⌊A⌋₊ - ⌊B⌋₊ + 1) = A := by
  unfold clampPt
  have h : ⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1) = ⌊A⌋₊ + 1 := by
    have := Nat.floor_le_floor (a := B) hBA; omega
  rw [h, min_eq_right (by push_cast; exact (Nat.lt_floor_add_one A).le), max_eq_right hBA]

theorem le_clampPt (B A : ℝ) (j : ℕ) : B ≤ clampPt B A j := le_max_left _ _

theorem clampPt_le {B A : ℝ} (hBA : B ≤ A) (j : ℕ) : clampPt B A j ≤ A :=
  max_le hBA (min_le_right _ _)

theorem clampPt_succ_le (B A : ℝ) (j : ℕ) : clampPt B A (j + 1) ≤ clampPt B A j + 1 := by
  unfold clampPt
  push_cast
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem clampPt_eq {B A : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hjA : ((⌊B⌋₊ + j : ℕ) : ℝ) ≤ A) : clampPt B A j = ((⌊B⌋₊ + j : ℕ) : ℝ) := by
  unfold clampPt
  rw [min_eq_left hjA, max_eq_right]
  have := Nat.lt_floor_add_one B
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  push_cast
  linarith

theorem floor_clampPt {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) (j : ℕ) :
    ⌊clampPt B A j⌋₊ = min (⌊B⌋₊ + j) ⌊A⌋₊ := by
  unfold clampPt
  set k := ⌊B⌋₊ + j with hk
  rcases le_or_gt (k : ℝ) A with hkA | hkA
  · rw [min_eq_left hkA, min_eq_left (Nat.le_floor hkA)]
    rcases le_or_gt B (k : ℝ) with hBk | hBk
    · rw [max_eq_right hBk, Nat.floor_natCast]
    · rw [max_eq_left hBk.le]
      have : k ≤ ⌊B⌋₊ := Nat.le_floor hBk.le
      omega
  · rw [min_eq_right hkA.le, max_eq_right hBA, min_eq_right]
    exact (Nat.cast_lt (α := ℝ)).1 ((Nat.floor_le (hB.trans hBA)).trans_lt hkA) |>.le

/-- `S x` only depends on `⌊x⌋₊`. -/
theorem S_eq_S_floor (x : ℝ) : S x = S (⌊x⌋₊ : ℝ) := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast]

theorem S_succ_sub (k : ℕ) :
    S ((k + 1 : ℕ) : ℝ) - S (k : ℝ) = if (k + 1).Prime then ((k + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast, Nat.floor_natCast, sum_range_succ]
  ring

/-- The primes `p` with `B < p ≤ A`. -/
noncomputable def primesIoc (B A : ℝ) : Finset ℕ := {p ∈ Ioc ⌊B⌋₊ ⌊A⌋₊ | p.Prime}

/-- The primes `p` with `B ≤ p ≤ A`. -/
noncomputable def primesIcc (B A : ℝ) : Finset ℕ := {p ∈ Icc ⌈B⌉₊ ⌊A⌋₊ | p.Prime}

/-- The primes `p` with `B < p < A`. -/
noncomputable def primesIoo (B A : ℝ) : Finset ℕ := {p ∈ Ioo ⌊B⌋₊ ⌈A⌉₊ | p.Prime}

theorem le_floor_iff_of_prime {p : ℕ} (hp : p.Prime) {A : ℝ} : p ≤ ⌊A⌋₊ ↔ (p : ℝ) ≤ A := by
  rcases le_or_gt 0 A with hA | hA
  · exact Nat.le_floor_iff hA
  · rw [Nat.floor_of_nonpos hA.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    constructor <;> intro h
    · exact absurd h (by have := hp.pos; omega)
    · linarith

theorem floor_lt_iff_of_prime {p : ℕ} (hp : p.Prime) {B : ℝ} : ⌊B⌋₊ < p ↔ B < p := by
  rcases le_or_gt 0 B with hB | hB
  · exact Nat.floor_lt hB
  · rw [Nat.floor_of_nonpos hB.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨fun _ ↦ by linarith, fun _ ↦ hp.pos⟩

theorem mem_primesIoc {B A : ℝ} {p : ℕ} : p ∈ primesIoc B A ↔ p.Prime ∧ B < p ∧ (p : ℝ) ≤ A := by
  simp only [primesIoc, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (floor_lt_iff_of_prime hp).1 h1, (le_floor_iff_of_prime hp).1 h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(floor_lt_iff_of_prime hp).2 h1, (le_floor_iff_of_prime hp).2 h2⟩, hp⟩

theorem mem_primesIcc {B A : ℝ} {p : ℕ} :
    p ∈ primesIcc B A ↔ p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A := by
  simp only [primesIcc, mem_filter, mem_Icc, Nat.ceil_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, h1, (le_floor_iff_of_prime hp).1 h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨h1, (le_floor_iff_of_prime hp).2 h2⟩, hp⟩

theorem mem_primesIoo {B A : ℝ} {p : ℕ} : p ∈ primesIoo B A ↔ p.Prime ∧ B < p ∧ (p : ℝ) < A := by
  simp only [primesIoo, mem_filter, mem_Ioo, Nat.lt_ceil]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (floor_lt_iff_of_prime hp).1 h1, h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(floor_lt_iff_of_prime hp).2 h1, h2⟩, hp⟩

/-- Summation by parts identity: the Stieltjes sum against `S` over the partition `clampPt`
is the sum over primes in `(B, A]`. -/
theorem sum_clampPt_eq (b : ℝ → ℝ) {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    ∑ j ∈ range (⌊A⌋₊ - ⌊B⌋₊ + 1),
        b (clampPt B A (j + 1)) * (S (clampPt B A (j + 1)) - S (clampPt B A j)) =
      ∑ p ∈ primesIoc B A, b p / p := by
  have hmN : ⌊B⌋₊ ≤ ⌊A⌋₊ := Nat.floor_le_floor hBA
  have hS : ∀ j, S (clampPt B A j) = S ((min (⌊B⌋₊ + j) ⌊A⌋₊ : ℕ) : ℝ) := fun j ↦ by
    rw [S_eq_S_floor, floor_clampPt hB hBA]
  rw [sum_range_succ, hS, hS, show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1)) ⌊A⌋₊ = ⌊A⌋₊ by omega,
    show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊)) ⌊A⌋₊ = ⌊A⌋₊ by omega, sub_self, mul_zero, add_zero,
    primesIoc, sum_filter, ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show ⌊A⌋₊ + 1 - (⌊B⌋₊ + 1) = ⌊A⌋₊ - ⌊B⌋₊ by omega]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj : j < ⌊A⌋₊ - ⌊B⌋₊ := mem_range.1 hj
  have hc : clampPt B A (j + 1) = ((⌊B⌋₊ + (j + 1) : ℕ) : ℝ) := by
    refine clampPt_eq (by omega) ?_
    exact (Nat.le_floor_iff (hB.trans hBA)).1 (by omega)
  rw [hS, hS, min_eq_left (by omega), min_eq_left (by omega), hc,
    show ⌊B⌋₊ + (j + 1) = ⌊B⌋₊ + j + 1 by ring, S_succ_sub, show ⌊B⌋₊ + 1 + j = ⌊B⌋₊ + j + 1 by ring]
  split_ifs <;> simp [div_eq_mul_inv]

theorem S_asymp_nonneg : ∃ c₅ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x := by
  obtain ⟨c₅, C, hC⟩ := S_asymp
  refine ⟨c₅, C, ?_, hC⟩
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hC 2 le_rfl)) (pntE_pos 2)

/-! ### Lemma 13 -/

/-- [I71, Lemma 13] for the primes in `(B, A]`. -/
theorem lemma13_Ioc : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ), 2 ≤ B → B ≤ A →
    MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIoc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨c₅, C, hC0, hC⟩ := S_asymp_nonneg
  refine ⟨2 + 2 * C, by linarith, fun b A B hB hBA hb hb0 ↦ ?_⟩
  set n := ⌊A⌋₊ - ⌊B⌋₊ + 1
  have h0 : clampPt B A 0 = B := clampPt_zero (by linarith)
  have hn : clampPt B A n = A := clampPt_last hBA
  have h2 : ∀ j, 2 ≤ clampPt B A j := fun j ↦ hB.trans (le_clampPt B A j)
  have hE : ∀ j, pntE (clampPt B A j) ≤ pntE B := fun j ↦
    pntE_le_pntE (by linarith) (le_clampPt B A j)
  have hFf : ∀ j < n, ∫ x in clampPt B A j..clampPt B A (j + 1), (x * log x)⁻¹ =
      (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) := by
    intro j _
    rw [integral_inv_mul_log (by linarith [h2 j]) (clampPt_mono B A (Nat.le_succ j))]
    ring
  have hδ : ∀ j < n, (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) ≤
      2 * pntE B := by
    intro j _
    have hj := h2 j
    have hlog : 0 < log (clampPt B A j) := log_pos (by linarith)
    calc _ = log (log (clampPt B A (j + 1))) - log (log (clampPt B A j)) := by ring
      _ ≤ (clampPt B A (j + 1) - clampPt B A j) / (clampPt B A j * log (clampPt B A j)) :=
          log_log_sub_log_log_le (by linarith) (clampPt_mono B A (Nat.le_succ j))
      _ ≤ 1 / (clampPt B A j * log (clampPt B A j)) := by
          gcongr
          linarith [clampPt_succ_le B A j]
      _ ≤ 2 * pntE (clampPt B A j) := one_div_mul_log_le_pntE hj
      _ ≤ 2 * pntE B := by linarith [hE j]
  have hε : ∀ j ≤ n, |S (clampPt B A j) - (log (log (clampPt B A j)) + c₅)| ≤ C * pntE B := by
    intro j _
    rw [← sub_sub]
    exact (hC _ (h2 j)).trans (mul_le_mul_of_nonneg_left (hE j) hC0)
  have key := abs_sum_sub_integral_le (n := n) (a := clampPt B A) (clampPt_mono B A)
    (b := b) (f := fun x ↦ (x * log x)⁻¹) (F := fun x ↦ log (log x) + c₅)
    (g := fun j ↦ S (clampPt B A j)) (by linarith [pntE_pos B]) (by rw [h0, hn]; exact hb)
    (by rw [h0]; exact hb0 B ⟨le_rfl, hBA⟩)
    (by
      rw [h0, hn]
      intro x hx
      have : 0 < log x := log_pos (by linarith [hx.1])
      have : 0 < x := by linarith [hx.1]
      positivity)
    (by rw [h0, hn]; exact continuousOn_inv_mul_log (by linarith)) hFf hδ hε
  rw [h0, hn, sum_clampPt_eq b (by linarith) hBA] at key
  simp_rw [div_eq_mul_inv (b _)]
  calc _ ≤ (2 * pntE B + 2 * (C * pntE B)) * b A := key
    _ = (2 + 2 * C) * b A * pntE B := by ring

end IwaniecJacobsthal
