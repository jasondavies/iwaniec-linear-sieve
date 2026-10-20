module

public import IwaniecLinearSieve.Rosser
public import IwaniecLinearSieve.PrimeSums.Product

@[expose] public section

/-!
# Notation with `k` ([I71, §1])

For `k : ℕ` (Iwaniec takes `k ≥ 1`) and a finite sequence `M` of integers, taken as a multiset
(Iwaniec writes `M = {a₁, …, aₙ}`; repeated values count with multiplicity):

* `primesLTk k z`: the primes `p < z` with `p ∤ k`;
* `Rk k z = R_k(z) = ∏_{p < z, p ∤ k} (1 - 1/p)`, with `Rk 1 z = R z` (`Rk_one`);
* `siftedCount k M z = A_k(M; z) = #{a ∈ M : no prime p < z with p ∤ k divides a}`;
* `multiplesCount M d = |M_d| = #{a ∈ M : d ∣ a}`.

We also prove [I71, (2.11)] for `R_k` (`Rk_eq`) and the comparison of `R_k` with `R` used for
[I71, (2.12), (2.13)]: `R_k(a)/R(a)` is increasing in `a` (`Rk_div_R_le_Rk_div_R`), so
`R_k(a) ≤ (R_k(b)/R(b)) R(a)` for `a ≤ b`, and `R(z) ≤ R_k(z)`.
-/

open Finset

namespace IwaniecLinearSieve

variable {k : ℕ} {z : ℝ} {p : ℕ}

theorem mem_primesLTk : p ∈ primesLTk k z ↔ p ∈ primesLT z ∧ ¬ p ∣ k :=
  mem_filter

theorem primesLTk_subset (k : ℕ) (z : ℝ) : primesLTk k z ⊆ primesLT z :=
  filter_subset _ _

theorem prime_of_mem_primesLTk (hp : p ∈ primesLTk k z) : p.Prime :=
  prime_of_mem_primesLT (primesLTk_subset k z hp)

@[simp] theorem primesLTk_one (z : ℝ) : primesLTk 1 z = primesLT z := by
  ext p
  simp only [mem_primesLTk, Nat.dvd_one, and_iff_left_iff_imp]
  exact fun hp ↦ (prime_of_mem_primesLT hp).one_lt.ne'

@[simp] theorem Rk_one (z : ℝ) : Rk 1 z = R z := by
  rw [Rk, primesLTk_one, R]

/-- For `p < z` with `p ∤ k`, the primes `q < z`, `q ∤ k` below `p` are those below `p`. -/
theorem filter_lt_primesLTk (hp : p ∈ primesLTk k z) :
    (primesLTk k z).filter (· < p) = primesLTk k p := by
  rw [primesLTk, filter_comm, filter_lt_primesLT (primesLTk_subset k z hp), primesLTk]

theorem primesLTk_natCast_subset (hp : p ∈ primesLTk k z) : primesLTk k p ⊆ primesLTk k z :=
  fun _ hq ↦ mem_primesLTk.2 ⟨primesLT_natCast_subset (primesLTk_subset k z hp)
    (mem_primesLTk.1 hq).1, (mem_primesLTk.1 hq).2⟩

theorem notMem_primesLTk_self : p ∉ primesLTk k p :=
  fun h ↦ notMem_primesLT_self (primesLTk_subset k p h)

theorem Rk_pos (k : ℕ) (z : ℝ) : 0 < Rk k z :=
  prod_pos fun _ hp ↦ one_sub_inv_pos (prime_of_mem_primesLTk hp)

theorem Rk_nonneg (k : ℕ) (z : ℝ) : 0 ≤ Rk k z := (Rk_pos k z).le

/-- [I71, (2.11)]: `R_k(z) = 1 - ∑_{p < z, p ∤ k} R_k(p) / p`. -/
theorem Rk_eq (k : ℕ) (z : ℝ) : Rk k z = 1 - ∑ p ∈ primesLTk k z, Rk k p / p := by
  rw [Rk, prod_one_sub_ordered]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [filter_lt_primesLTk hp, Rk, div_eq_inv_mul]

/-- The factor `∏_{p < z, p ∣ k} (1 - 1/p)` by which `R(z)` and `R_k(z)` differ. -/
noncomputable def RkDefect (k : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ (primesLT z).filter (· ∣ k), (1 - (p : ℝ)⁻¹)

theorem RkDefect_pos (k : ℕ) (z : ℝ) : 0 < RkDefect k z :=
  prod_pos fun _ hp ↦ one_sub_inv_pos (prime_of_mem_primesLT (mem_filter.1 hp).1)

theorem RkDefect_le_one (k : ℕ) (z : ℝ) : RkDefect k z ≤ 1 :=
  prod_le_one₀ (fun _ hp ↦ (one_sub_inv_pos (prime_of_mem_primesLT (mem_filter.1 hp).1)).le)
    fun p _ ↦ one_sub_inv_le_one p

theorem RkDefect_antitone (k : ℕ) : Antitone (RkDefect k) := fun a b hab ↦ by
  have hsub : (primesLT a).filter (· ∣ k) ⊆ (primesLT b).filter (· ∣ k) :=
    filter_subset_filter _ (primesLT_mono hab)
  rw [RkDefect, RkDefect, ← prod_sdiff hsub]
  refine mul_le_of_le_one_left (RkDefect_pos k a).le (prod_le_one₀ (fun p hp ↦ ?_)
    fun p _ ↦ one_sub_inv_le_one p)
  exact (one_sub_inv_pos (prime_of_mem_primesLT (mem_filter.1 (mem_sdiff.1 hp).1).1)).le

/-- `R(z) = R_k(z) ∏_{p < z, p ∣ k} (1 - 1/p)`. -/
theorem R_eq_Rk_mul (k : ℕ) (z : ℝ) : R z = Rk k z * RkDefect k z := by
  rw [R, Rk, RkDefect, primesLTk, mul_comm, prod_filter_mul_prod_filter_not]

theorem Rk_div_R (k : ℕ) (z : ℝ) : Rk k z / R z = (RkDefect k z)⁻¹ := by
  rw [R_eq_Rk_mul k z, div_mul_cancel_left₀ (Rk_pos k z).ne']

/-- `R(z) ≤ R_k(z)`. -/
theorem R_le_Rk (k : ℕ) (z : ℝ) : R z ≤ Rk k z := by
  rw [R_eq_Rk_mul k z]
  exact mul_le_of_le_one_right (Rk_nonneg k z) (RkDefect_le_one k z)

theorem one_le_Rk_div_R (k : ℕ) (z : ℝ) : 1 ≤ Rk k z / R z :=
  (one_le_div (R_pos z)).2 (R_le_Rk k z)

/-- `R_k(a) / R(a)` is increasing in `a`. -/
theorem Rk_div_R_le_Rk_div_R (k : ℕ) {a b : ℝ} (hab : a ≤ b) : Rk k a / R a ≤ Rk k b / R b := by
  rw [Rk_div_R, Rk_div_R]
  exact inv_anti₀ (RkDefect_pos k b) (RkDefect_antitone k hab)

/-- [I71, p. 6]: for `a ≤ b`, `R_k(a) ≤ (R_k(b) / R(b)) R(a)`. -/
theorem Rk_le_mul_R (k : ℕ) {a b : ℝ} (hab : a ≤ b) : Rk k a ≤ Rk k b / R b * R a := by
  have := Rk_div_R_le_Rk_div_R k hab
  rwa [div_le_iff₀ (R_pos a)] at this

end IwaniecLinearSieve
