module

public import IwaniecLinearSieve.Jacobsthal.ShiftedSieve

@[expose] public section

/-!
# [I78, Lemma 1] (the shifted sieve) in full

Let `𝒜 = (a_i)_{i ∈ A}` be a finite sequence of integers and `Q = ∏_{q ∈ S} q` a product of
distinct primes, with `|𝒜_d| = #{i ∈ A : d ∣ a_i}` satisfying

    (R)   ||𝒜_d| - X / f(d)| ≤ A B^{τ(d)}     for all d ∣ Q,

and let `P = ∏_{p ∈ T} p` be another squarefree number with a one-one multiplicative
correspondence `l` between the divisors of `Q` and of `P`, with `g(n) ≤ f(d)` for `n = l(d)`
([I78, (2)]). [I78, Lemma 1] states: for real weights `(λ_n)_{n ∣ P}` with partial sums
`σ_m = ∑_{n ∣ m} λ_n`,

    (3)   S(𝒜, Q) ≤ X ∏_{q ∣ Q} (1 - 1/f(q)) ∑_{n ∣ P} σ_n / ∏_{p ∣ n} (g(p) - 1)
                      + A ∑_{n ∣ P} |λ_n| B^{τ(n)}     if σ_m ≥ ∑_{n ∣ m} μ(n) for all m ∣ P,
    (4)   S(𝒜, Q) ≥ X ∏_{q ∣ Q} (1 - 1/f(q)) ∑_{n ∣ P} σ_n / ∏_{p ∣ n} (g(p) - 1)
                      - A ∑_{n ∣ P} |λ_n| B^{τ(n)}     if σ_m ≤ ∑_{n ∣ m} μ(n) for all m ∣ P,

where `S(𝒜, Q) = #{i ∈ A : (a_i, Q) = 1}`. [I78] proves only (4); `shiftedSieve_upper` proves (3)
by the same argument.

Formalisation. Divisors of squarefree numbers are sets of primes, and the multiplicative
functions `f`, `g` are given by their values at primes (`f(d) = ∏_{q ∣ d} f(q)`); `τ(d) = 2^{ω(d)}`
for squarefree `d`. The correspondence `l` is given by the matching `e = l⁻¹ : T → S` of the
primes (a multiplicative bijection of divisors is determined by the primes), and the weights are
`w : Finset ℕ → ℝ` on the subsets of `T`. Deviations from [I78]:

* **the signs in the conditions are interchanged in print**: [I78] prints `(+) σ_m ≤ ∑ μ(n)` for
  (3) and `(−) σ_m ≥ ∑ μ(n)` for (4). The proof of (4) begins with
  `S(𝒜, Q) ≥ ∑_{a} ∑_{d ∣ (a, Q)} λ_{l(d)}`, which needs `σ_m ≤ [m = 1] = ∑_{n ∣ m} μ(n)`, and
  [I78, §3] applies (4) to Rosser's lower-bound weights, which satisfy `σ_m ≤ [m = 1]`;
* `g(p) > 1` (not `≥ 1`) at the primes `p ∣ P`, since (3) and (4) divide by `g(p) - 1`;
* `X ≥ 0`; no conditions on `A`, `B` (those of [I78] are `A, B, X ≥ 1`);
* (2) is only used for primes, `g(p) ≤ f(e(p))`, which is how it is assumed here.

The special case used for Jacobsthal's problem (`f(d) = d`, `g(n) = n`, `A = B = 1`, `𝒜` an
interval, Rosser's weights) is also proved directly, as `shiftedSieve`, for `iwaniecBound`.
-/

open Finset

namespace IwaniecLinearSieve

variable {ι : Type*} {S T : Finset ℕ} {e : ℕ → ℕ}

/-- For distinct primes `e(p)`, `p ∈ C`: `∏_{p ∈ C} e(p) ∣ a ↔ C ⊆ {p ∈ T : e(p) ∣ a}`. -/
theorem prod_dvd_iff_subset_filter (hS : ∀ q ∈ S, q.Prime) (he : Set.BijOn e T S)
    {C : Finset ℕ} (hC : C ⊆ T) (a : ℤ) :
    ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a ↔ C ⊆ T.filter fun p ↦ (e p : ℤ) ∣ a := by
  constructor
  · intro h p hp
    refine mem_filter.2 ⟨hC hp, (Int.natCast_dvd_natCast.2 ?_).trans h⟩
    exact dvd_prod_of_mem _ hp
  · intro h
    rw [Nat.cast_prod]
    refine prod_dvd_of_coprime ?_ fun p hp ↦ (mem_filter.1 (h hp)).2
    intro p hp q hq hpq
    refine Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hS _ (he.mapsTo (hC hp)))
      (hS _ (he.mapsTo (hC hq)))).2 fun h' ↦ hpq (he.injOn (hC hp) (hC hq) h'))

/-- `∑_{d ∣ (a, Q)} λ_{l(d)} = σ_{l((a, Q))}`, as sums over subsets. -/
theorem sum_powerset_mul_ite_dvd (hS : ∀ q ∈ S, q.Prime) (he : Set.BijOn e T S)
    (w : Finset ℕ → ℝ) (a : ℤ) :
    ∑ C ∈ T.powerset, w C * (if ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a then 1 else 0) =
      ∑ C ∈ (T.filter fun p ↦ (e p : ℤ) ∣ a).powerset, w C := by
  have h : (T.filter fun p ↦ (e p : ℤ) ∣ a).powerset =
      T.powerset.filter (· ⊆ T.filter fun p ↦ (e p : ℤ) ∣ a) := by
    ext C
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h ↦ ⟨h.trans (filter_subset _ _), h⟩, fun h ↦ h.2⟩
  rw [h, sum_filter]
  refine sum_congr rfl fun C hC ↦ ?_
  simp only [prod_dvd_iff_subset_filter hS he (mem_powerset.1 hC)]
  split_ifs <;> simp

/-- `(a, Q) = 1` iff no `e(p)` divides `a`. -/
theorem filter_dvd_eq_empty_iff (he : Set.BijOn e T S) (a : ℤ) :
    (T.filter fun p ↦ (e p : ℤ) ∣ a) = ∅ ↔ ∀ q ∈ S, ¬ (q : ℤ) ∣ a := by
  rw [filter_eq_empty_iff]
  constructor
  · intro h q hq hqa
    obtain ⟨p, hp, rfl⟩ := he.surjOn hq
    exact h hp hqa
  · intro h p hp
    exact h _ (he.mapsTo hp)

/-- `∑_{d ∣ Q} λ_{l(d)} / f(d) = ∏_{q ∣ Q} (1 - 1/f(q)) ∑_{d ∣ Q} σ_{l(d)} / ∏_{q ∣ d} (f(q) - 1)`,
transported to the subsets of `T`. -/
theorem sum_powerset_div_prod_comp (he : Set.BijOn e T S) (f : ℕ → ℝ)
    (hf : ∀ p ∈ T, 1 < f (e p)) (w : Finset ℕ → ℝ) :
    ∑ C ∈ T.powerset, w C / ∏ p ∈ C, f (e p) =
      (∏ q ∈ S, (1 - (f q)⁻¹)) *
        ∑ B ∈ T.powerset, (∑ C ∈ B.powerset, w C) / ∏ p ∈ B, (f (e p) - 1) := by
  rw [sum_powerset_div_prod T (fun p ↦ f (e p))
    (fun p hp ↦ ⟨(zero_lt_one.trans (hf p hp)).ne', (hf p hp).ne'⟩) w]
  congr 1
  exact prod_nbij e (fun p hp ↦ he.mapsTo hp) he.injOn he.surjOn fun p _ ↦ rfl

/-- The comparison of main terms in [I78, Lemma 1]: if `σ(B) ≤ 0` for nonempty `B` and
`1 < g ≤ f` on `T`, then `∑ σ(B) / ∏_B (g - 1) ≤ ∑ σ(B) / ∏_B (f - 1)`. -/
theorem sum_div_prod_sub_one_le (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f p) (σ : Finset ℕ → ℝ) (hσ : ∀ B ⊆ T, B.Nonempty → σ B ≤ 0) :
    ∑ B ∈ T.powerset, σ B / ∏ p ∈ B, (g p - 1) ≤ ∑ B ∈ T.powerset, σ B / ∏ p ∈ B, (f p - 1) := by
  refine sum_le_sum fun B hB ↦ ?_
  rw [mem_powerset] at hB
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp
  have h0 : 0 < ∏ p ∈ B, (g p - 1) := prod_pos fun p hp ↦ sub_pos.2 (hg p (hB hp))
  have h1 : ∏ p ∈ B, (g p - 1) ≤ ∏ p ∈ B, (f p - 1) :=
    prod_le_prod₀ (fun p hp ↦ (sub_pos.2 (hg p (hB hp))).le)
      fun p hp ↦ sub_le_sub_right (hgf p (hB hp)) 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonpos_left (inv_anti₀ h0 h1) (hσ B hB hBne)

/-- The same comparison for `σ(B) ≥ 0` on nonempty `B`, in the other direction. -/
theorem sum_div_prod_sub_one_le' (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f p) (σ : Finset ℕ → ℝ) (hσ : ∀ B ⊆ T, B.Nonempty → 0 ≤ σ B) :
    ∑ B ∈ T.powerset, σ B / ∏ p ∈ B, (f p - 1) ≤ ∑ B ∈ T.powerset, σ B / ∏ p ∈ B, (g p - 1) := by
  have := sum_div_prod_sub_one_le f g hg hgf (fun B ↦ -σ B)
    fun B hB hBne ↦ neg_nonpos.2 (hσ B hB hBne)
  simp only [neg_div, sum_neg_distrib, neg_le_neg_iff] at this
  exact this

/-- Condition (R) at `d = ∏_{p ∈ C} e(p)`, for `C ⊆ T`. -/
theorem abs_card_sub_le_of_R (A : Finset ι) (a : ι → ℤ) (he : Set.BijOn e T S) (f : ℕ → ℝ)
    {X Ac Bc : ℝ}
    (hR : ∀ D ⊆ S, |(#{i ∈ A | ((∏ q ∈ D, q : ℕ) : ℤ) ∣ a i} : ℝ) - X / ∏ q ∈ D, f q| ≤
      Ac * Bc ^ (2 ^ #D))
    {C : Finset ℕ} (hC : C ⊆ T) :
    |(#{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} : ℝ) - X / ∏ p ∈ C, f (e p)| ≤
      Ac * Bc ^ (2 ^ #C) := by
  have hinj : Set.InjOn e C := he.injOn.mono hC
  have h := hR (C.image e) fun q hq ↦ by
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    exact he.mapsTo (hC hp)
  rwa [prod_image hinj, prod_image hinj, card_image_of_injOn hinj] at h

/-- The sieve inequality summed over `𝒜`: `∑_{d ∣ Q} λ_{l(d)} |𝒜_d| = ∑_{a ∈ 𝒜} σ_{l((a, Q))}`. -/
theorem sum_mul_card_eq (A : Finset ι) (a : ι → ℤ) (hS : ∀ q ∈ S, q.Prime)
    (he : Set.BijOn e T S) (w : Finset ℕ → ℝ) :
    ∑ C ∈ T.powerset, w C * #{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} =
      ∑ i ∈ A, ∑ C ∈ (T.filter fun p ↦ (e p : ℤ) ∣ a i).powerset, w C := by
  simp_rw [natCast_card_filter, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_powerset_mul_ite_dvd hS he w (a i)

theorem prod_one_sub_inv_nonneg (he : Set.BijOn e T S) (f : ℕ → ℝ)
    (hf : ∀ p ∈ T, 1 < f (e p)) : 0 ≤ ∏ q ∈ S, (1 - (f q)⁻¹) := by
  refine prod_nonneg fun q hq ↦ ?_
  obtain ⟨p, hp, rfl⟩ := he.surjOn hq
  exact sub_nonneg.2 (inv_le_one_of_one_le₀ (hf p hp).le)

theorem sum_mul_div_eq_mul_sum (T : Finset ℕ) (w : Finset ℕ → ℝ) (h : Finset ℕ → ℝ) (X : ℝ) :
    ∑ C ∈ T.powerset, w C * X / h C = X * ∑ C ∈ T.powerset, w C / h C := by
  rw [mul_sum]
  exact sum_congr rfl fun C _ ↦ by ring

/-- **[I78, Lemma 1], (4)** (the shifted sieve, lower bound): if `σ(B) = ∑_{C ⊆ B} w(C)` satisfies
`σ(B) ≤ [B = ∅]` for all `B ⊆ T` (i.e. `σ_m ≤ ∑_{n ∣ m} μ(n)` for `m ∣ P`), then
`S(𝒜, Q) ≥ X ∏_{q ∣ Q} (1 - 1/f(q)) ∑_{n ∣ P} σ_n / ∏_{p ∣ n} (g(p) - 1)
  - A ∑_{n ∣ P} |λ_n| B^{τ(n)}`.
-/
theorem shiftedSieve_lower (A : Finset ι) (a : ι → ℤ) (hS : ∀ q ∈ S, q.Prime)
    (he : Set.BijOn e T S) (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f (e p)) {X Ac Bc : ℝ} (hX : 0 ≤ X)
    (hR : ∀ D ⊆ S, |(#{i ∈ A | ((∏ q ∈ D, q : ℕ) : ℤ) ∣ a i} : ℝ) - X / ∏ q ∈ D, f q| ≤
      Ac * Bc ^ (2 ^ #D))
    (w : Finset ℕ → ℝ) (hw : ∀ B ⊆ T, ∑ C ∈ B.powerset, w C ≤ if B = ∅ then 1 else 0) :
    X * (∏ q ∈ S, (1 - (f q)⁻¹)) *
          ∑ B ∈ T.powerset, (∑ C ∈ B.powerset, w C) / ∏ p ∈ B, (g p - 1) -
        Ac * ∑ C ∈ T.powerset, |w C| * Bc ^ (2 ^ #C) ≤
      #{i ∈ A | ∀ q ∈ S, ¬ (q : ℤ) ∣ a i} := by
  have hf : ∀ p ∈ T, 1 < f (e p) := fun p hp ↦ (hg p hp).trans_le (hgf p hp)
  -- `∑_{d ∣ Q} λ_{l(d)} |𝒜_d| ≤ S(𝒜, Q)`
  have hcount : ∑ C ∈ T.powerset, w C * #{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} ≤
      #{i ∈ A | ∀ q ∈ S, ¬ (q : ℤ) ∣ a i} := by
    rw [sum_mul_card_eq A a hS he w, natCast_card_filter]
    refine sum_le_sum fun i _ ↦ ?_
    refine (hw _ (filter_subset _ _)).trans_eq ?_
    simp only [filter_dvd_eq_empty_iff he]
  -- the remainder, by (R)
  have hrem : ∀ C ∈ T.powerset, w C * X / ∏ p ∈ C, f (e p) - |w C| * (Ac * Bc ^ (2 ^ #C)) ≤
      w C * #{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} := by
    intro C hC
    have h := abs_card_sub_le_of_R A a he f hR (mem_powerset.1 hC)
    set N : ℝ := (#{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} : ℝ)
    have h' : |w C * (N - X / ∏ p ∈ C, f (e p))| ≤ |w C| * (Ac * Bc ^ (2 ^ #C)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have := neg_abs_le (w C * (N - X / ∏ p ∈ C, f (e p)))
    rw [mul_div_assoc]
    linarith [mul_sub (w C) N (X / ∏ p ∈ C, f (e p))]
  -- the main term
  have hmain : X * (∏ q ∈ S, (1 - (f q)⁻¹)) *
        ∑ B ∈ T.powerset, (∑ C ∈ B.powerset, w C) / ∏ p ∈ B, (g p - 1) ≤
      ∑ C ∈ T.powerset, w C * X / ∏ p ∈ C, f (e p) := by
    rw [sum_mul_div_eq_mul_sum, sum_powerset_div_prod_comp he f hf w, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
      (prod_one_sub_inv_nonneg he f hf)) hX
    exact sum_div_prod_sub_one_le (fun p ↦ f (e p)) g hg hgf _ fun B hB hBne ↦ by
      simpa [hBne.ne_empty] using hw B hB
  have hsum := sum_le_sum hrem
  rw [sum_sub_distrib] at hsum
  have hAc : ∑ C ∈ T.powerset, |w C| * (Ac * Bc ^ (2 ^ #C)) =
      Ac * ∑ C ∈ T.powerset, |w C| * Bc ^ (2 ^ #C) := by
    rw [mul_sum]
    exact sum_congr rfl fun C _ ↦ by ring
  linarith

/-- **[I78, Lemma 1], (3)** (the shifted sieve, upper bound): if `σ(B) = ∑_{C ⊆ B} w(C)`
satisfies `σ(B) ≥ [B = ∅]` for all `B ⊆ T` (i.e. `σ_m ≥ ∑_{n ∣ m} μ(n)` for `m ∣ P`), then
`S(𝒜, Q) ≤ X ∏_{q ∣ Q} (1 - 1/f(q)) ∑_{n ∣ P} σ_n / ∏_{p ∣ n} (g(p) - 1)
  + A ∑_{n ∣ P} |λ_n| B^{τ(n)}`.
[I78] states (3) without proof. -/
theorem shiftedSieve_upper (A : Finset ι) (a : ι → ℤ) (hS : ∀ q ∈ S, q.Prime)
    (he : Set.BijOn e T S) (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f (e p)) {X Ac Bc : ℝ} (hX : 0 ≤ X)
    (hR : ∀ D ⊆ S, |(#{i ∈ A | ((∏ q ∈ D, q : ℕ) : ℤ) ∣ a i} : ℝ) - X / ∏ q ∈ D, f q| ≤
      Ac * Bc ^ (2 ^ #D))
    (w : Finset ℕ → ℝ) (hw : ∀ B ⊆ T, (if B = ∅ then 1 else 0) ≤ ∑ C ∈ B.powerset, w C) :
    (#{i ∈ A | ∀ q ∈ S, ¬ (q : ℤ) ∣ a i} : ℝ) ≤
      X * (∏ q ∈ S, (1 - (f q)⁻¹)) *
          ∑ B ∈ T.powerset, (∑ C ∈ B.powerset, w C) / ∏ p ∈ B, (g p - 1) +
        Ac * ∑ C ∈ T.powerset, |w C| * Bc ^ (2 ^ #C) := by
  have hf : ∀ p ∈ T, 1 < f (e p) := fun p hp ↦ (hg p hp).trans_le (hgf p hp)
  have hcount : (#{i ∈ A | ∀ q ∈ S, ¬ (q : ℤ) ∣ a i} : ℝ) ≤
      ∑ C ∈ T.powerset, w C * #{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} := by
    rw [sum_mul_card_eq A a hS he w, natCast_card_filter]
    refine sum_le_sum fun i _ ↦ ?_
    refine le_of_eq_of_le ?_ (hw _ (filter_subset _ _))
    simp only [filter_dvd_eq_empty_iff he]
  have hrem : ∀ C ∈ T.powerset, w C * #{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} ≤
      w C * X / ∏ p ∈ C, f (e p) + |w C| * (Ac * Bc ^ (2 ^ #C)) := by
    intro C hC
    have h := abs_card_sub_le_of_R A a he f hR (mem_powerset.1 hC)
    set N : ℝ := (#{i ∈ A | ((∏ p ∈ C, e p : ℕ) : ℤ) ∣ a i} : ℝ)
    have h' : |w C * (N - X / ∏ p ∈ C, f (e p))| ≤ |w C| * (Ac * Bc ^ (2 ^ #C)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have := le_abs_self (w C * (N - X / ∏ p ∈ C, f (e p)))
    rw [mul_div_assoc]
    linarith [mul_sub (w C) N (X / ∏ p ∈ C, f (e p))]
  have hmain : ∑ C ∈ T.powerset, w C * X / ∏ p ∈ C, f (e p) ≤
      X * (∏ q ∈ S, (1 - (f q)⁻¹)) *
        ∑ B ∈ T.powerset, (∑ C ∈ B.powerset, w C) / ∏ p ∈ B, (g p - 1) := by
    rw [sum_mul_div_eq_mul_sum, sum_powerset_div_prod_comp he f hf w, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
      (prod_one_sub_inv_nonneg he f hf)) hX
    exact sum_div_prod_sub_one_le' (fun p ↦ f (e p)) g hg hgf _ fun B hB hBne ↦ by
      simpa [hBne.ne_empty] using hw B hB
  have hsum := sum_le_sum hrem
  rw [sum_add_distrib] at hsum
  have hAc : ∑ C ∈ T.powerset, |w C| * (Ac * Bc ^ (2 ^ #C)) =
      Ac * ∑ C ∈ T.powerset, |w C| * Bc ^ (2 ^ #C) := by
    rw [mul_sum]
    exact sum_congr rfl fun C _ ↦ by ring
  linarith

end IwaniecLinearSieve
