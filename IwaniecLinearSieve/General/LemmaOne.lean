module

public import IwaniecLinearSieve.General.Defs

@[expose] public section

/-!
# The general principles of sieve ([I71, §2], Lemmas 1, 2, (2.5)–(2.8), (2.12), (2.13))

Let `f : List ℕ → ℝ` be arbitrary truncation functions: `f [p₁, …, pᵢ]` is Iwaniec's
`fᵢ(p₁, …, pᵢ)`. The depth-`n` sieve support `truncSet f k lower n h z` is the set of products
`d = p₁ ⋯ p_l`, `l ≤ n`, of primes `z > p₁ > ⋯ > p_l` with `pᵢ ∤ k`, subject to
`p_{i+1} < f [p₁, …, pᵢ]` (after the history `h`) at every level `i` of the right parity:
the levels where the recursion is at `lower = false`. Concretely the recursion is

    truncSet f k lower 0 h z = {1}
    truncSet f k lower (n+1) h z = {1} ∪ ⋃_{p ∈ truncPrimes f k lower h z}
      p · truncSet f k (!lower) n (h ++ [p]) p

where `truncPrimes f k lower h z` consists of the primes `p < z`, `p ∤ k`, with `p < f h` unless
`lower = true`. Thus `truncSet f k false (2r) [] z` is the support of [I71, (2.1)] (with the extra
condition `p₁ < f []`; take `f [] ≥ z` to recover [I71] literally) and
`truncSet f k true (2r - 1) [] z` is the support of [I71, (2.2)].

* Lemma 1 (`lemma1_upper`, `lemma1_lower`, and their parity-general forms `siftedCount_le_sum`,
  `sum_le_siftedCount`): `A_k(M; z) ≤ ∑_{d ∈ D⁺} μ(d) |M_d|` and
  `A_k(M; z) ≥ ∑_{d ∈ D⁻} μ(d) |M_d|`.
* Corollary ((2.5)–(2.8); `lemma1_cor_upper`, `lemma1_cor_lower`): under
  `(*) |M_d - y/d| ≤ 1` for squarefree `d` with `(d, k) = 1`, `A_k(M; z) ≤ y G_{r,k}(z) + Σ₁(z)` and
  `A_k(M; z) ≥ y D_{r,k}(z) - Σ₂(z)`, with `G, D = truncMain` and `Σ₁, Σ₂` the support sizes.
* Lemma 2 (`truncMain_false_eq`, `truncMain_true_eq`): `G_{r,k} = S_{r,k}` and `D_{r,k} = T_{r,k}`,
  where `S_{r,k} = R_k + truncDef f k false (2r) [] z` and `T_{r,k} = R_k - truncDef f k true
  (2r-1) [] z`; `truncDef` is the recursive form of the sums (2.9), (2.10).
* (2.12), (2.13) (`truncMain_false_le`, `le_truncMain_true`):
  `S_{r,k}(z) ≤ (R_k(z)/R(z)) S_{r,1}(z)` and `T_{r,k}(z) ≥ (R_k(z)/R(z)) T_{r,1}(z)`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace IwaniecLinearSieve

variable (f : List ℕ → ℝ) (k : ℕ)

/-- The primes admitted at the next level of the truncated sieve: `p < z`, `p ∤ k`, and
`p < f h` unless `lower = true`. -/
noncomputable def truncPrimes (lower : Bool) (h : List ℕ) (z : ℝ) : Finset ℕ :=
  (primesLTk k z).filter fun p ↦ lower = true ∨ (p : ℝ) < f h

/-- The depth-`n` support of the sieve with truncation functions `f` ([I71, Lemma 1]). -/
noncomputable def truncSet : Bool → ℕ → List ℕ → ℝ → Finset ℕ
  | _, 0, _, _ => {1}
  | lower, n + 1, h, z => insert 1 ((truncPrimes f k lower h z).biUnion fun p ↦
      (truncSet (!lower) n (h ++ [p]) p).image (p * ·))

variable {f k} {lower : Bool} {n : ℕ} {h : List ℕ} {z : ℝ} {p d : ℕ}

theorem mem_truncPrimes :
    p ∈ truncPrimes f k lower h z ↔ p ∈ primesLTk k z ∧ (lower = true ∨ (p : ℝ) < f h) :=
  mem_filter

theorem truncPrimes_subset : truncPrimes f k lower h z ⊆ primesLTk k z := filter_subset _ _

@[simp] theorem truncPrimes_true : truncPrimes f k true h z = primesLTk k z := by
  simp [truncPrimes]

@[simp] theorem truncSet_zero (lower : Bool) (h : List ℕ) (z : ℝ) :
    truncSet f k lower 0 h z = {1} := by
  cases lower <;> rfl

theorem truncSet_succ (lower : Bool) (n : ℕ) (h : List ℕ) (z : ℝ) :
    truncSet f k lower (n + 1) h z = insert 1 ((truncPrimes f k lower h z).biUnion fun p ↦
      (truncSet f k (!lower) n (h ++ [p]) p).image (p * ·)) := by
  cases lower <;> rfl

theorem one_mem_truncSet : 1 ∈ truncSet f k lower n h z := by
  cases n with
  | zero => simp
  | succ n => rw [truncSet_succ]; exact mem_insert_self _ _

theorem mem_truncSet_succ : d ∈ truncSet f k lower (n + 1) h z ↔
    d = 1 ∨ ∃ p ∈ truncPrimes f k lower h z, ∃ e ∈ truncSet f k (!lower) n (h ++ [p]) p,
      d = p * e := by
  rw [truncSet_succ]
  simp [eq_comm (a := d)]

/-- Elements of `truncSet` are squarefree products of primes `p < z` with `p ∤ k`. -/
theorem squarefree_and_primeFactors_subset_truncSet (hd : d ∈ truncSet f k lower n h z) :
    Squarefree d ∧ d.primeFactors ⊆ primesLTk k z := by
  induction n generalizing lower h z d with
  | zero =>
    rw [truncSet_zero, mem_singleton] at hd
    simp [hd]
  | succ n ih =>
    rcases mem_truncSet_succ.1 hd with rfl | ⟨p, hp, e, he, rfl⟩
    · simp
    have hpz := truncPrimes_subset hp
    have hpp := prime_of_mem_primesLTk hpz
    obtain ⟨hse, hpe⟩ := ih he
    have hne : ¬ p ∣ e := fun h ↦
      notMem_primesLTk_self (hpe (Nat.mem_primeFactors.2 ⟨hpp, h, hse.ne_zero⟩))
    refine ⟨Nat.squarefree_mul_iff.2 ⟨(Nat.Prime.coprime_iff_not_dvd hpp).2 hne,
      hpp.squarefree, hse⟩, ?_⟩
    rw [Nat.primeFactors_mul hpp.ne_zero hse.ne_zero, hpp.primeFactors]
    exact union_subset (singleton_subset_iff.2 hpz) (hpe.trans (primesLTk_natCast_subset hpz))

theorem pos_of_mem_truncSet (hd : d ∈ truncSet f k lower n h z) : 0 < d :=
  Nat.pos_of_ne_zero (squarefree_and_primeFactors_subset_truncSet hd).1.ne_zero

theorem lt_of_prime_dvd_of_mem_truncSet {q : ℕ} (hq : q.Prime)
    (hd : d ∈ truncSet f k lower n h z) (hqd : q ∣ d) : (q : ℝ) < z :=
  lt_of_mem_primesLT <| primesLTk_subset k z <|
    (squarefree_and_primeFactors_subset_truncSet hd).2 <|
      Nat.mem_primeFactors.2 ⟨hq, hqd, (pos_of_mem_truncSet hd).ne'⟩

theorem not_dvd_of_mem_truncSet (hp : p.Prime) (hd : d ∈ truncSet f k lower n h p) : ¬ p ∣ d :=
  fun h ↦ (lt_irrefl _) (lt_of_prime_dvd_of_mem_truncSet hp hd h)

/-- Elements of `truncSet` are coprime to `k`. -/
theorem coprime_of_mem_truncSet (hd : d ∈ truncSet f k lower n h z) : d.Coprime k := by
  refine Nat.coprime_of_dvd fun q hq hqd hqk ↦ ?_
  have := (squarefree_and_primeFactors_subset_truncSet hd).2
    (Nat.mem_primeFactors.2 ⟨hq, hqd, (pos_of_mem_truncSet hd).ne'⟩)
  exact (mem_primesLTk.1 this).2 hqk

theorem pairwiseDisjoint_truncSet_image (lower : Bool) (n : ℕ) (h : List ℕ) (z : ℝ) :
    (truncPrimes f k lower h z : Set ℕ).PairwiseDisjoint fun p ↦
      (truncSet f k (!lower) n (h ++ [p]) p).image (p * ·) := by
  intro p hp q hq hpq
  simp only [Function.onFun]
  rw [disjoint_left]
  simp only [mem_image, not_exists, not_and]
  rintro _ ⟨d, hd, rfl⟩ e he hde
  have hp' := prime_of_mem_primesLTk (truncPrimes_subset hp)
  have hq' := prime_of_mem_primesLTk (truncPrimes_subset hq)
  have key : ∀ {p q d e : ℕ}, p.Prime → q.Prime → p ≠ q →
      e ∈ truncSet f k (!lower) n (h ++ [q]) q → q * e = p * d → (p : ℝ) < q := by
    intro p q d e hp hq hpq he h
    have : p ∣ q * e := h ▸ dvd_mul_right p d
    rcases (Nat.Prime.dvd_mul hp).1 this with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).1 h') hpq
    · exact lt_of_prime_dvd_of_mem_truncSet hp he h'
  exact lt_asymm (key hp' hq' hpq he hde) (key hq' hp' (Ne.symm hpq) hd hde.symm)

theorem one_notMem_biUnion_truncSet (lower : Bool) (n : ℕ) (h : List ℕ) (z : ℝ) :
    1 ∉ (truncPrimes f k lower h z).biUnion fun p ↦
      (truncSet f k (!lower) n (h ++ [p]) p).image (p * ·) := by
  simp only [mem_biUnion, mem_image, not_exists, not_and]
  intro p hp d _ h
  exact (prime_of_mem_primesLTk (truncPrimes_subset hp)).one_lt.ne'
    (Nat.eq_one_of_mul_eq_one_right h)

/-- Sums over `truncSet` unfold along the recursion. -/
theorem sum_truncSet_succ {M : Type*} [AddCommMonoid M] (g : ℕ → M) (lower : Bool) (n : ℕ)
    (h : List ℕ) (z : ℝ) :
    ∑ d ∈ truncSet f k lower (n + 1) h z, g d =
      g 1 + ∑ p ∈ truncPrimes f k lower h z,
        ∑ d ∈ truncSet f k (!lower) n (h ++ [p]) p, g (p * d) := by
  rw [truncSet_succ, sum_insert (one_notMem_biUnion_truncSet lower n h z),
    sum_biUnion (pairwiseDisjoint_truncSet_image lower n h z)]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [sum_image]
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_left (prime_of_mem_primesLTk (truncPrimes_subset hp)).pos h

theorem moebius_mul_of_mem_truncSet (hp : p.Prime) (hd : d ∈ truncSet f k lower n h p) :
    μ (p * d) = -μ d := by
  rw [isMultiplicative_moebius.map_mul_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_mem_truncSet hp hd)),
    moebius_apply_prime hp, neg_one_mul]

/-! ### Lemma 1 for a single integer -/

/-- `1` if no prime `p < z` with `p ∤ k` divides `m`, and `0` otherwise. -/
noncomputable def siftIndicatorK (k : ℕ) (z : ℝ) (m : ℕ) : ℤ :=
  if ∀ p ∈ primesLTk k z, ¬ p ∣ m then 1 else 0

theorem siftIndicatorK_nonneg (k : ℕ) (z : ℝ) (m : ℕ) : 0 ≤ siftIndicatorK k z m := by
  unfold siftIndicatorK
  split_ifs <;> norm_num

theorem siftIndicatorK_le_one (k : ℕ) (z : ℝ) (m : ℕ) : siftIndicatorK k z m ≤ 1 := by
  unfold siftIndicatorK
  split_ifs <;> norm_num

/-- [I71, (2.3)] for a single integer (Buchstab's identity):
`[(m, P_k(z)) = 1] = 1 - ∑_{p < z, p ∤ k, p ∣ m} [(m, P_k(p)) = 1]`. -/
theorem siftIndicatorK_eq (k : ℕ) (z : ℝ) (m : ℕ) :
    siftIndicatorK k z m = 1 - ∑ p ∈ (primesLTk k z).filter (· ∣ m), siftIndicatorK k p m := by
  set F := (primesLTk k z).filter (· ∣ m)
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF, sum_empty, sub_zero, siftIndicatorK, ite_eq_left]
    intro p hp hpm
    have : p ∈ F := mem_filter.2 ⟨hp, hpm⟩
    simp [hF] at this
  set p₀ := F.min' hF
  have hp₀ : p₀ ∈ F := F.min'_mem hF
  have hsum : ∑ p ∈ F, siftIndicatorK k p m = ∑ p ∈ F, if p = p₀ then 1 else 0 := by
    refine sum_congr rfl fun p hp ↦ ?_
    rw [siftIndicatorK]
    have hpz := (mem_filter.1 hp).1
    congr 1
    apply propext
    constructor
    · intro h
      refine le_antisymm ?_ (F.min'_le p hp)
      by_contra hlt
      have hp₀k := (mem_filter.1 hp₀).1
      refine h p₀ (mem_primesLTk.2 ⟨mem_primesLT.2 ⟨prime_of_mem_primesLTk hp₀k,
        by exact_mod_cast not_le.1 hlt⟩, (mem_primesLTk.1 hp₀k).2⟩) (mem_filter.1 hp₀).2
    · rintro rfl q hq hqm
      have hqF : q ∈ F := mem_filter.2 ⟨primesLTk_natCast_subset hpz hq, hqm⟩
      exact absurd (F.min'_le q hqF)
        (not_le.2 (by exact_mod_cast lt_of_mem_primesLT (primesLTk_subset k _ hq)))
  rw [hsum, sum_ite_eq' F p₀, ite_eq_left hp₀, siftIndicatorK, ite_eq_right]
  · norm_num
  · push Not
    exact ⟨p₀, (mem_filter.1 hp₀).1, (mem_filter.1 hp₀).2⟩

/-- `∑_{d ∈ truncSet, d ∣ m} μ(d)`. -/
noncomputable def truncSieve (f : List ℕ → ℝ) (k : ℕ) (lower : Bool) (n : ℕ) (h : List ℕ)
    (z : ℝ) (m : ℕ) : ℤ :=
  ∑ d ∈ (truncSet f k lower n h z).filter (· ∣ m), μ d

theorem truncSieve_zero (lower : Bool) (h : List ℕ) (z : ℝ) (m : ℕ) :
    truncSieve f k lower 0 h z m = 1 := by
  simp [truncSieve, filter_singleton]

theorem truncSieve_succ (lower : Bool) (n : ℕ) (h : List ℕ) (z : ℝ) (m : ℕ) :
    truncSieve f k lower (n + 1) h z m = 1 - ∑ p ∈ (truncPrimes f k lower h z).filter (· ∣ m),
      truncSieve f k (!lower) n (h ++ [p]) p m := by
  rw [truncSieve, sum_filter, sum_truncSet_succ, sum_filter, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [one_dvd, ite_true, moebius_apply_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLTk (truncPrimes_subset hp)
  split_ifs with hpm
  · rw [truncSieve, sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun d hd ↦ ?_
    have key : p * d ∣ m ↔ d ∣ m :=
      ⟨fun h ↦ (dvd_mul_left d p).trans h, fun h ↦ Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((Nat.Prime.coprime_iff_not_dvd hp').2 (not_dvd_of_mem_truncSet hp' hd)) hpm h⟩
    simp only [key, moebius_mul_of_mem_truncSet hp' hd]
    split_ifs <;> simp
  · refine sum_eq_zero fun d _ ↦ ?_
    rw [ite_eq_right]
    exact fun h ↦ hpm ((dvd_mul_right p d).trans h)

/-- [I71, Lemma 1] for a single integer `m`: for even `n` the upper-bound weights, and for odd
`n` the lower-bound weights, satisfy the sieve inequalities. -/
theorem truncSieve_sift (n : ℕ) :
    (Even n → ∀ h z m, siftIndicatorK k z m ≤ truncSieve f k false n h z m) ∧
      (Odd n → ∀ h z m, truncSieve f k true n h z m ≤ siftIndicatorK k z m) := by
  induction n with
  | zero =>
    refine ⟨fun _ h z m ↦ ?_, fun h ↦ absurd h (by decide)⟩
    rw [truncSieve_zero]
    exact siftIndicatorK_le_one k z m
  | succ n ih =>
    constructor
    · intro hn h z m
      have hodd : Odd n := Nat.not_even_iff_odd.1 (Nat.even_add_one.1 hn)
      rw [truncSieve_succ, siftIndicatorK_eq]
      refine sub_le_sub_left ?_ _
      calc ∑ p ∈ (truncPrimes f k false h z).filter (· ∣ m),
            truncSieve f k (!false) n (h ++ [p]) p m
          ≤ ∑ p ∈ (truncPrimes f k false h z).filter (· ∣ m), siftIndicatorK k p m :=
            sum_le_sum fun p _ ↦ ih.2 hodd _ _ _
        _ ≤ ∑ p ∈ (primesLTk k z).filter (· ∣ m), siftIndicatorK k p m :=
            sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ truncPrimes_subset)
              fun p _ _ ↦ siftIndicatorK_nonneg k p m
    · intro hn h z m
      have heven : Even n := by simpa [Nat.odd_add_one] using hn
      rw [truncSieve_succ, siftIndicatorK_eq, truncPrimes_true]
      exact sub_le_sub_left (sum_le_sum fun p _ ↦ ih.1 heven _ _ _) _

/-! ### Lemma 1 for finite sequences of integers -/

/-- `∑_{d ∈ D} μ(d) |M_d| = ∑_{a ∈ M} ∑_{d ∈ D, d ∣ a} μ(d)`. -/
theorem sum_moebius_mul_multiplesCount (D : Finset ℕ) (M : Multiset ℤ) :
    ∑ d ∈ D, μ d * (multiplesCount M d : ℤ) =
      (M.map fun a ↦ ∑ d ∈ D.filter (· ∣ a.natAbs), μ d).sum := by
  induction M using Multiset.induction_on with
  | empty => simp [multiplesCount]
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun d _ ↦ ?_
    simp only [multiplesCount, Multiset.countP_cons, Int.natCast_dvd]
    split_ifs <;> push_cast <;> ring

theorem siftedCount_eq_sum (k : ℕ) (M : Multiset ℤ) (z : ℝ) :
    (siftedCount k M z : ℤ) = (M.map fun a ↦ siftIndicatorK k z a.natAbs).sum := by
  induction M using Multiset.induction_on with
  | empty => simp [siftedCount]
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih]
    simp only [siftedCount, Multiset.countP_cons, siftIndicatorK, Int.natCast_dvd]
    split_ifs <;> push_cast <;> ring

/-- [I71, (2.1)] for any even depth `n`:
`A_k(M; z) ≤ ∑_{d ∈ D⁺} μ(d) |M_d|`. -/
theorem siftedCount_le_sum (hn : Even n) (h : List ℕ) (M : Multiset ℤ) (z : ℝ) :
    (siftedCount k M z : ℤ) ≤
      ∑ d ∈ truncSet f k false n h z, μ d * (multiplesCount M d : ℤ) := by
  rw [siftedCount_eq_sum, sum_moebius_mul_multiplesCount]
  exact Multiset.sum_map_le_sum_map _ _ fun a _ ↦ (truncSieve_sift n).1 hn h z a.natAbs

/-- [I71, (2.2)] for any odd depth `n`:
`A_k(M; z) ≥ ∑_{d ∈ D⁻} μ(d) |M_d|`. -/
theorem sum_le_siftedCount (hn : Odd n) (h : List ℕ) (M : Multiset ℤ) (z : ℝ) :
    ∑ d ∈ truncSet f k true n h z, μ d * (multiplesCount M d : ℤ) ≤
      (siftedCount k M z : ℤ) := by
  rw [siftedCount_eq_sum, sum_moebius_mul_multiplesCount]
  exact Multiset.sum_map_le_sum_map _ _ fun a _ ↦ (truncSieve_sift n).2 hn h z a.natAbs

/-- [I71, Lemma 1, (2.1)]: for arbitrary truncation functions `f`, every `r` and `z`,
`A_k(M; z) ≤ |M| - ∑ |M_{p₁}| + ∑ |M_{p₁p₂}| - ⋯ + ∑ |M_{p₁⋯p_{2r}}|`, the sums running over
`p_{2r} < ⋯ < p₁ < z`, `pᵢ ∤ k`, with `p_{2i+1} < f_{2i}(p₁, …, p_{2i})`. -/
theorem lemma1_upper (f : List ℕ → ℝ) (k r : ℕ) (M : Multiset ℤ) (z : ℝ) :
    (siftedCount k M z : ℤ) ≤
      ∑ d ∈ truncSet f k false (2 * r) [] z, μ d * (multiplesCount M d : ℤ) :=
  siftedCount_le_sum (even_two_mul r) [] M z

/-- [I71, Lemma 1, (2.2)]: for arbitrary truncation functions `f`, every `r ≥ 1` and `z`,
`A_k(M; z) ≥ |M| - ∑ |M_{p₁}| + ∑ |M_{p₁p₂}| - ⋯ - ∑ |M_{p₁⋯p_{2r-1}}|`, the sums running over
`p_{2r-1} < ⋯ < p₁ < z`, `pᵢ ∤ k`, with `p_{2i} < f_{2i-1}(p₁, …, p_{2i-1})`. -/
theorem lemma1_lower (f : List ℕ → ℝ) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) (M : Multiset ℤ) (z : ℝ) :
    ∑ d ∈ truncSet f k true (2 * r - 1) [] z, μ d * (multiplesCount M d : ℤ) ≤
      (siftedCount k M z : ℤ) :=
  sum_le_siftedCount (Nat.Even.sub_odd (by omega) (even_two_mul r) odd_one) [] M z

/-! ### The Corollary to Lemma 1: (2.5)–(2.8) -/

/-- The main sums `G_{r,k}(z)`, `D_{r,k}(z)` of [I71, (2.7), (2.8)]:
`∑_{d ∈ truncSet} μ(d) / d`. -/
noncomputable def truncMain (f : List ℕ → ℝ) (k : ℕ) (lower : Bool) (n : ℕ) (h : List ℕ)
    (z : ℝ) : ℝ :=
  ∑ d ∈ truncSet f k lower n h z, (μ d : ℝ) / d

theorem sum_moebius_mul_le_of_approx {D : Finset ℕ} {M : Multiset ℤ} {y : ℝ}
    (hM : ∀ d ∈ D, |(multiplesCount M d : ℝ) - y / d| ≤ 1) :
    |∑ d ∈ D, (μ d : ℝ) * multiplesCount M d - y * ∑ d ∈ D, (μ d : ℝ) / d| ≤ #D := by
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum]
  refine sum_le_sum fun d hd ↦ ?_
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  rw [show (μ d : ℝ) * multiplesCount M d - y * ((μ d : ℝ) / d) =
      (μ d : ℝ) * (multiplesCount M d - y / d) by ring, abs_mul, Nat.cast_one]
  calc |(μ d : ℝ)| * |(multiplesCount M d : ℝ) - y / d| ≤ 1 * 1 :=
        mul_le_mul hμ (hM d hd) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- [I71, (2.5), (2.7)] for any even depth: under `(*) |M_d - y/d| ≤ 1` for squarefree `d`
with `(d, k) = 1`,
`A_k(M; z) ≤ y G(z) + Σ₁(z)` with `Σ₁(z) = #D⁺`. -/
theorem lemma1_cor_upper (hn : Even n) (h : List ℕ) {M : Multiset ℤ} {y : ℝ}
    (hM : ∀ d : ℕ, Squarefree d → d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    (siftedCount k M z : ℝ) ≤
      y * truncMain f k false n h z + #(truncSet f k false n h z) := by
  have h1 : (siftedCount k M z : ℝ) ≤
      ∑ d ∈ truncSet f k false n h z, (μ d : ℝ) * multiplesCount M d := by
    exact_mod_cast siftedCount_le_sum hn h M z
  have h2 := sum_moebius_mul_le_of_approx (D := truncSet f k false n h z) (M := M) (y := y)
    fun d hd ↦ hM d (squarefree_and_primeFactors_subset_truncSet hd).1
      (coprime_of_mem_truncSet hd)
  rw [truncMain]
  linarith [le_abs_self (∑ d ∈ truncSet f k false n h z, (μ d : ℝ) * multiplesCount M d -
    y * ∑ d ∈ truncSet f k false n h z, (μ d : ℝ) / d)]

/-- [I71, (2.6), (2.8)] for any odd depth: under `(*) |M_d - y/d| ≤ 1` for squarefree `d`
with `(d, k) = 1`,
`A_k(M; z) ≥ y D(z) - Σ₂(z)` with `Σ₂(z) = #D⁻`. -/
theorem lemma1_cor_lower (hn : Odd n) (h : List ℕ) {M : Multiset ℤ} {y : ℝ}
    (hM : ∀ d : ℕ, Squarefree d → d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) (z : ℝ) :
    y * truncMain f k true n h z - #(truncSet f k true n h z) ≤ (siftedCount k M z : ℝ) := by
  have h1 : ∑ d ∈ truncSet f k true n h z, (μ d : ℝ) * multiplesCount M d ≤
      (siftedCount k M z : ℝ) := by
    exact_mod_cast sum_le_siftedCount hn h M z
  have h2 := sum_moebius_mul_le_of_approx (D := truncSet f k true n h z) (M := M) (y := y)
    fun d hd ↦ hM d (squarefree_and_primeFactors_subset_truncSet hd).1
      (coprime_of_mem_truncSet hd)
  rw [truncMain]
  linarith [neg_abs_le (∑ d ∈ truncSet f k true n h z, (μ d : ℝ) * multiplesCount M d -
    y * ∑ d ∈ truncSet f k true n h z, (μ d : ℝ) / d)]

/-! ### Lemma 2: `G_{r,k} = S_{r,k}`, `D_{r,k} = T_{r,k}` -/

theorem truncMain_zero (lower : Bool) (h : List ℕ) (z : ℝ) : truncMain f k lower 0 h z = 1 := by
  simp [truncMain]

theorem truncMain_succ (lower : Bool) (n : ℕ) (h : List ℕ) (z : ℝ) :
    truncMain f k lower (n + 1) h z =
      1 - ∑ p ∈ truncPrimes f k lower h z, truncMain f k (!lower) n (h ++ [p]) p / p := by
  rw [truncMain, sum_truncSet_succ, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [moebius_apply_one, Int.cast_one, Nat.cast_one, div_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLTk (truncPrimes_subset hp)
  rw [truncMain, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [moebius_mul_of_mem_truncSet hp' hd]
  push_cast
  field_simp

theorem truncPrimes_false :
    truncPrimes f k false h z = (primesLTk k z).filter fun p : ℕ ↦ (p : ℝ) < f h := by
  simp [truncPrimes]

/-- The deficits `S_{r,k}(z) - R_k(z)` (for `lower = false`) and `R_k(z) - T_{r,k}(z)` (for
`lower = true`), i.e. the sums of [I71, (2.9), (2.10)] over the tuples that fail a truncation
condition, together with the full tuples of maximal length, in recursive form. -/
noncomputable def truncDef (f : List ℕ → ℝ) (k : ℕ) : Bool → ℕ → List ℕ → ℝ → ℝ
  | false, 0, _, z => ∑ p ∈ primesLTk k z, Rk k p / p
  | true, 0, _, z => -∑ p ∈ primesLTk k z, Rk k p / p
  | true, n + 1, h, z => ∑ p ∈ primesLTk k z, truncDef f k false n (h ++ [p]) p / p
  | false, n + 1, h, z => ∑ p ∈ truncPrimes f k false h z, truncDef f k true n (h ++ [p]) p / p +
      ∑ p ∈ (primesLTk k z).filter (fun p : ℕ ↦ ¬ (p : ℝ) < f h), Rk k p / p

/-- [I71, Lemma 2] at every depth: `G = R_k + (S - R_k)` and `D = R_k - (R_k - T)`. -/
theorem truncMain_eq (n : ℕ) (h : List ℕ) (z : ℝ) :
    truncMain f k false n h z = Rk k z + truncDef f k false n h z ∧
      truncMain f k true n h z = Rk k z - truncDef f k true n h z := by
  induction n generalizing h z with
  | zero =>
    simp only [truncMain_zero, truncDef]
    constructor <;> linarith [Rk_eq k z]
  | succ n ih =>
    constructor
    · rw [truncMain_succ, truncDef, Rk_eq k z, truncPrimes_false,
        ← sum_filter_add_sum_filter_not (primesLTk k z) (fun p : ℕ ↦ (p : ℝ) < f h)
          (fun p ↦ Rk k p / p)]
      simp only [Bool.not_false]
      have : ∑ p ∈ (primesLTk k z).filter (fun p : ℕ ↦ (p : ℝ) < f h),
          truncMain f k true n (h ++ [p]) p / p =
          ∑ p ∈ (primesLTk k z).filter (fun p : ℕ ↦ (p : ℝ) < f h), Rk k p / p -
            ∑ p ∈ (primesLTk k z).filter (fun p : ℕ ↦ (p : ℝ) < f h),
              truncDef f k true n (h ++ [p]) p / p := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun p _ ↦ ?_
        rw [(ih _ _).2, sub_div]
      rw [this]
      ring
    · rw [truncMain_succ, truncDef, Rk_eq k z, truncPrimes_true]
      simp only [Bool.not_true]
      rw [sub_sub, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun p _ ↦ ?_
      rw [(ih _ _).1, add_div]

/-- [I71, Lemma 2], `G_{r,k}(z) = S_{r,k}(z)`. -/
theorem truncMain_false_eq (n : ℕ) (h : List ℕ) (z : ℝ) :
    truncMain f k false n h z = Rk k z + truncDef f k false n h z :=
  (truncMain_eq n h z).1

/-- [I71, Lemma 2], `D_{r,k}(z) = T_{r,k}(z)`. -/
theorem truncMain_true_eq (n : ℕ) (h : List ℕ) (z : ℝ) :
    truncMain f k true n h z = Rk k z - truncDef f k true n h z :=
  (truncMain_eq n h z).2

/-- The deficits are nonnegative at the depths of Lemma 1 (even for the upper sieve, odd for
the lower sieve). -/
theorem truncDef_nonneg (n : ℕ) :
    (Even n → ∀ h z, 0 ≤ truncDef f k false n h z) ∧
      (Odd n → ∀ h z, 0 ≤ truncDef f k true n h z) := by
  induction n with
  | zero =>
    refine ⟨fun _ h z ↦ ?_, fun h ↦ absurd h (by decide)⟩
    exact sum_nonneg fun p _ ↦ div_nonneg (Rk_nonneg k p) p.cast_nonneg
  | succ n ih =>
    constructor
    · intro hn h z
      have hodd : Odd n := Nat.not_even_iff_odd.1 (Nat.even_add_one.1 hn)
      exact add_nonneg (sum_nonneg fun p _ ↦ div_nonneg (ih.2 hodd _ _) p.cast_nonneg)
        (sum_nonneg fun p _ ↦ div_nonneg (Rk_nonneg k p) p.cast_nonneg)
    · intro hn h z
      have heven : Even n := by simpa [Nat.odd_add_one] using hn
      exact sum_nonneg fun p _ ↦ div_nonneg (ih.1 heven _ _) p.cast_nonneg

theorem truncPrimes_subset_one (lower : Bool) (h : List ℕ) (z : ℝ) :
    truncPrimes f k lower h z ⊆ truncPrimes f 1 lower h z := by
  intro p hp
  rw [mem_truncPrimes] at hp ⊢
  exact ⟨by rw [primesLTk_one]; exact primesLTk_subset k z hp.1, hp.2⟩

/-- The deficits for `k` are at most `R_k(z)/R(z)` times those for `k = 1`. -/
theorem truncDef_le (n : ℕ) :
    (Even n → ∀ h z, truncDef f k false n h z ≤ Rk k z / R z * truncDef f 1 false n h z) ∧
      (Odd n → ∀ h z, truncDef f k true n h z ≤ Rk k z / R z * truncDef f 1 true n h z) := by
  have hc : ∀ z, 0 ≤ Rk k z / R z := fun z ↦ div_nonneg (Rk_nonneg k z) (R_nonneg z)
  have hmono : ∀ {p : ℕ} {z : ℝ}, p ∈ primesLTk k z → Rk k p / R p ≤ Rk k z / R z :=
    fun hp ↦ Rk_div_R_le_Rk_div_R k (lt_of_mem_primesLT (primesLTk_subset _ _ hp)).le
  have hbase : ∀ (z : ℝ) (s t : Finset ℕ), s ⊆ t → s ⊆ primesLTk k z →
      ∑ p ∈ s, Rk k p / p ≤ Rk k z / R z * ∑ p ∈ t, Rk 1 p / p := by
    intro z s t hst hs
    rw [mul_sum]
    refine (sum_le_sum fun p hp ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg hst
      fun p _ _ ↦ mul_nonneg (hc z) (div_nonneg (Rk_nonneg 1 p) p.cast_nonneg))
    rw [Rk_one, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (Rk_le_mul_R k (lt_of_mem_primesLT (primesLTk_subset _ _ (hs hp))).le) p.cast_nonneg
  induction n with
  | zero =>
    refine ⟨fun _ h z ↦ ?_, fun h ↦ absurd h (by decide)⟩
    simp only [truncDef]
    exact hbase z _ _ (by rw [primesLTk_one]; exact primesLTk_subset k z) subset_rfl
  | succ n ih =>
    constructor
    · intro hn h z
      have hodd : Odd n := Nat.not_even_iff_odd.1 (Nat.even_add_one.1 hn)
      simp only [truncDef]
      rw [mul_add]
      refine add_le_add ?_ (hbase z _ _ ?_ (filter_subset _ _))
      · rw [mul_sum]
        refine (sum_le_sum fun p hp ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg
          (truncPrimes_subset_one false h z) fun p _ _ ↦ mul_nonneg (hc z)
            (div_nonneg ((truncDef_nonneg n).2 hodd _ _) p.cast_nonneg))
        rw [← mul_div_assoc]
        refine div_le_div_of_nonneg_right ((ih.2 hodd _ _).trans ?_) p.cast_nonneg
        exact mul_le_mul_of_nonneg_right (hmono (truncPrimes_subset hp))
          ((truncDef_nonneg n).2 hodd _ _)
      · intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨by rw [primesLTk_one]; exact primesLTk_subset k z hp.1, hp.2⟩
    · intro hn h z
      have heven : Even n := by simpa [Nat.odd_add_one] using hn
      simp only [truncDef]
      rw [mul_sum]
      refine (sum_le_sum fun p hp ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg
        (by rw [primesLTk_one]; exact primesLTk_subset k z) fun p _ _ ↦ mul_nonneg (hc z)
          (div_nonneg ((truncDef_nonneg n).1 heven _ _) p.cast_nonneg))
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ((ih.1 heven _ _).trans ?_) p.cast_nonneg
      exact mul_le_mul_of_nonneg_right (hmono hp) ((truncDef_nonneg n).1 heven _ _)

/-- [I71, (2.12)]: `S_{r,k}(z) ≤ (R_k(z)/R(z)) S_{r,1}(z)`, i.e. (by Lemma 2)
`G_{r,k}(z) ≤ (R_k(z)/R(z)) G_{r,1}(z)`, at any even depth. -/
theorem truncMain_false_le (hn : Even n) (h : List ℕ) (z : ℝ) :
    truncMain f k false n h z ≤ Rk k z / R z * truncMain f 1 false n h z := by
  rw [truncMain_false_eq, truncMain_false_eq, Rk_one, mul_add,
    div_mul_cancel₀ _ (R_pos z).ne']
  exact add_le_add_right ((truncDef_le n).1 hn h z) _

/-- [I71, (2.13)]: `T_{r,k}(z) ≥ (R_k(z)/R(z)) T_{r,1}(z)`, i.e. (by Lemma 2)
`D_{r,k}(z) ≥ (R_k(z)/R(z)) D_{r,1}(z)`, at any odd depth. -/
theorem le_truncMain_true (hn : Odd n) (h : List ℕ) (z : ℝ) :
    Rk k z / R z * truncMain f 1 true n h z ≤ truncMain f k true n h z := by
  rw [truncMain_true_eq, truncMain_true_eq, Rk_one, mul_sub,
    div_mul_cancel₀ _ (R_pos z).ne']
  exact sub_le_sub_left ((truncDef_le n).2 hn h z) _

end IwaniecLinearSieve
