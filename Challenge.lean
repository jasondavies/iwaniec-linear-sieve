module

public import Mathlib

@[expose] public section

/-!
# Advertised statements

* [I71] H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30.
* [I78] H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231.

This file is the statement surface to audit. It states:

* [I78, Corollary] (Jacobsthal's problem): if `m` consecutive integers are each divisible by one
  of `r ≥ 2` given primes, then `m ≤ C (r log r)²`;
* [I78, Theorem]: an interval of length `c ∏ (1 - 1/q)⁻¹ r² log r` contains at least `r²`
  integers coprime to `r ≥ 2` given primes;
* [I71, Theorem 1]: the linear sieve bounds (1.1), (1.2) at the sifting limit, with the stated
  formulas for `f`, `F` and the asymptotics of `𝔐`;
* [I71, Corollary]: the bounds (1.3), (1.4);
* [I71, Theorem 2]: `C₀(r) ≪ r² log² r` for Jacobsthal's function of the first `r` primes;
* [I71, Theorem 3]: the asymptotic formulas (1.5), (1.6) for `A_k(M; z)`.

The [I78] statements and [I71, Theorem 2] use only Mathlib. The [I71] sieve statements use the
definitions below, copied verbatim from `IwaniecLinearSieve/Definitions.lean`; Comparator checks
that they are the same constants as in the solution.

The sieve hypothesis `(*)` of [I71] for a finite sequence `M` of integers (a multiset, so
repeated terms count with multiplicity), a modulus `k` and a level `y` is
`∀ d : ℕ, d.Coprime k → |multiplesCount M d - y / d| ≤ 1`.
-/

open Real Finset

namespace IwaniecLinearSieve

/-! ## Sifted sets ([I71, §1]) -/

/-- The primes `p < z`. -/
noncomputable def primesLT (z : ℝ) : Finset ℕ := Nat.primesBelow ⌈z⌉₊

/-- The primes `p < z` with `p ∤ k`. -/
noncomputable def primesLTk (k : ℕ) (z : ℝ) : Finset ℕ := (primesLT z).filter fun p ↦ ¬ p ∣ k

/-- Iwaniec's `R_k(z) = ∏_{p < z, p ∤ k} (1 - 1/p)`. -/
noncomputable def Rk (k : ℕ) (z : ℝ) : ℝ := ∏ p ∈ primesLTk k z, (1 - (p : ℝ)⁻¹)

/-- Iwaniec's `A_k(M; z)`: the number of terms of `M` not divisible by any prime `p < z`
with `p ∤ k`. -/
noncomputable def siftedCount (k : ℕ) (M : Multiset ℤ) (z : ℝ) : ℕ :=
  M.countP fun a ↦ ∀ p ∈ primesLTk k z, ¬ (p : ℤ) ∣ a

/-- Iwaniec's `|M_d|`: the number of terms of `M` divisible by `d`. -/
def multiplesCount (M : Multiset ℤ) (d : ℕ) : ℕ := M.countP fun a ↦ (d : ℤ) ∣ a

/-! ## The sieve functions `f` and `F` ([I71, §3, (3.1)–(3.7)]) -/

/-- The formula `3 log (3 / (s - 1)) + s - 4` for `g₂` on `[2, 4]`. -/
noncomputable def gTwoFormula (s : ℝ) : ℝ := 3 * log (3 / (s - 1)) + s - 4

/-- Left end of the domain of `g i` in [I71]: `2` for even `i`, `3` for odd `i`. -/
noncomputable def gLower (i : ℕ) : ℝ := if Even i then 2 else 3

/-- The kernel `t ↦ h (t - 1) / (t - 1)`, with the denominator replaced by `max (t - 1) 1` so that
it is continuous on `ℝ` whenever `h` is. It agrees with `h (t - 1) / (t - 1)` for `t ≥ 2`. -/
noncomputable def shiftKernel (h : ℝ → ℝ) (t : ℝ) : ℝ := h (t - 1) / max (t - 1) 1

/-- Iwaniec's functions `g_n` of [I71, (3.1)–(3.3)], extended to all of `ℝ`:
`g₂(s) = 3 log (3 / (s - 1)) + s - 4` on `[2, 4]` and `0` for `s ≥ 4`, and
`g_{n+1}(s) = ∫_s^∞ g_n(t - 1) / (t - 1) dt` for `s` at least `gLower (n + 1)`.
Outside the domains of [I71] the argument is clamped: the even functions are constant on
`s ≤ 2`, the odd ones on `s ≤ 3`, and `g 0 = g 1 = 0`. The upper limit `n + 5 = (n + 3) + 2`
of the integral can replace `∞` because `g (n + 2) s = 0` for `s ≥ n + 4`. -/
noncomputable def g : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, s => gTwoFormula (max 2 (min s 4))
  | n + 3, s => ∫ t in max s (gLower (n + 3))..((n : ℝ) + 5), shiftKernel (g (n + 2)) t

/-- Iwaniec's `f(s) = Σ_{i ≥ 1} g_{2i}(s)` [I71, (3.6)]; constant (`= f(2) = 2`) for `s ≤ 2`. -/
noncomputable def fSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 2) s

/-- Iwaniec's `F(s) = Σ_{i ≥ 1} g_{2i+1}(s)` [I71, (3.7)]; constant (`= F(3)`) for `s ≤ 3`. -/
noncomputable def FSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 3) s

/-! ## The function `𝔐` ([I71, §3, Definition]) -/

namespace Delay

/-- One Picard-type step: `y₀` up to `3`, then integrate `k x * y (x - 1)` from `3`. -/
noncomputable def step (k y₀ y : ℝ → ℝ) (s : ℝ) : ℝ :=
  y₀ (min s 3) + ∫ x in (3 : ℝ)..max s 3, k x * y (x - 1)

/-- The iterates of `step`; the `n`-th one is correct on `(-∞, n + 3]`. -/
noncomputable def iter (k y₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y₀
  | n + 1 => step k y₀ (iter k y₀ n)

/-- The solution `y` of the delay equation `y s = y₀ s` for `s ≤ 3` and
`y s = y₀ 3 + ∫ x in 3..s, k x * y (x - 1)` for `s ≥ 3`. -/
noncomputable def sol (k y₀ : ℝ → ℝ) (s : ℝ) : ℝ := iter k y₀ ⌈s⌉₊ s

end Delay

/-- The kernel `x / (x - 1)²` of the delay equations, frozen to the left of `3`. -/
noncomputable def delayKer (x : ℝ) : ℝ := max x 3 / (max x 3 - 1) ^ 2

/-- Initial values of `𝔚` on `[2, 3]` (constant to the left of `2`). -/
noncomputable def initW (s : ℝ) : ℝ := 1 / (max s 2 - 1) - log (max s 2 - 1)

/-- Iwaniec's `𝔐` [I71, §3, Definition]: `𝔐(s) = 2 + 1/(s - 1) - log (s - 1)` on `[2, 3]`
(constant `3` to the left of `2`) and `𝔐'(s) = -s/(s - 1)² 𝔐(s - 1)` for `s > 3`. -/
noncomputable def bigM : ℝ → ℝ := Delay.sol (fun x => -delayKer x) (fun s => 2 + initW s)

/-! ## Statements -/

/-- **[I78, Corollary]**: if `m` consecutive integers `x, …, x + m - 1` are each divisible by
one of `r ≥ 2` given primes, then `m ≤ C (r log r)²` for an absolute constant `C`. -/
theorem iwaniecBound :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
  sorry

/-- **[I78, Theorem]**: there is an absolute constant `c > 0` such that for any `r ≥ 2` primes
`S`, any `X ≥ c ∏_{q ∈ S} (1 - 1/q)⁻¹ r² log r` consecutive integers `x, …, x + X - 1` contain at
least `r²` integers coprime to `∏_{q ∈ S} q`. -/
theorem iwaniec_theorem : ∃ c : ℝ, 0 < c ∧ ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → 2 ≤ #S →
    ∀ (x : ℤ) (X : ℕ), c * (∏ q ∈ S, (1 - (q : ℝ)⁻¹))⁻¹ * ((#S : ℝ) ^ 2 * log #S) ≤ X →
      #S ^ 2 ≤ #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  sorry

/-- **[I71, Theorem 1]**, with the formulas for `f`, `F` and `𝔐` stated there. Under `(*)`, with
`z = y^{1/s}` and `s ≤ log y / (log log 3y)^{11/5}`:
(1.1) `A_k(M; z) < y R_k(z) (1 + F(s)/s + E)` for `s ≥ 3`, and
(1.2) `A_k(M; z) > y R_k(z) (1 - f(s)/s - E)` for `s ≥ 2`, where
`E = c₀ (1 + s² log⁵ s / log² y)^{5s} 𝔐(s) log log 3k / log y`. Moreover
`f(s) = s - 2e^γ log (s - 1)` on `[2, 4]`,
`F(s) = 2e^γ (1 + ∫_1^{s-2} log x / (x + 1) dx) - s` on `[3, 5]` (the printed formula has a sign
slip; this is the correct one), and
`log 𝔐(s) = -s (log s + log log s - 1 + log log s / log s) + O(s / log s)`. -/
theorem theorem1_full :
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y s : ℝ), 1 < y →
      (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) →
      s ≤ log y / log (log (3 * y)) ^ (11 / 5 : ℝ) →
      (3 ≤ s → (siftedCount k M (y ^ (1 / s)) : ℝ) <
        y * Rk k (y ^ (1 / s)) * (1 + FSieve s / s +
          c₀ * (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s) * bigM s * log (log (3 * k)) /
            log y)) ∧
      (2 ≤ s → y * Rk k (y ^ (1 / s)) * (1 - fSieve s / s -
          c₀ * (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s) * bigM s * log (log (3 * k)) /
            log y) < siftedCount k M (y ^ (1 / s)))) ∧
    (∀ s ∈ Set.Icc (2 : ℝ) 4, fSieve s = s - 2 * exp eulerMascheroniConstant * log (s - 1)) ∧
    (∀ s ∈ Set.Icc (3 : ℝ) 5, FSieve s =
      2 * exp eulerMascheroniConstant * (1 + ∫ x in (1 : ℝ)..(s - 2), log x / (x + 1)) - s) ∧
    (∃ C s₀ : ℝ, ∀ s ≥ s₀, |log (bigM s) +
      s * (log s + log (log s) - 1 + log (log s) / log s)| ≤ C * s / log s) := by
  sorry

/-- **[I71, Corollary]**, (1.3): under `(*)`, for `2 ≤ z ≤ y` and `s = log y / log z`,
`A_k(M; z) < y R_k(z) (1 + (F(s) + (3 - s)⁺)/s + e₁ log log 3k / log y)`.
For `s ≥ 3` this is (1.3) as printed; for `1 ≤ s < 3` the term `(3 - s)⁺` corrects for `F` being
constant below 3 (the paper gives no range for `z`). -/
theorem corollary_upper : ∃ e₁ : ℝ, 0 ≤ e₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y z : ℝ),
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z → z ≤ y →
    (siftedCount k M z : ℝ) < y * Rk k z * (1 + (FSieve (log y / log z) +
      max (3 - log y / log z) 0) / (log y / log z) + e₁ * log (log (3 * k)) / log y) := by
  sorry

/-- **[I71, Corollary]**, (1.4): under `(*)`, for `y > 1`, `z ≥ 2` and `s = log y / log z`,
`A_k(M; z) > y R_k(z) (1 - f(s)/s - e₁ log log 3k / log y)`. -/
theorem corollary_lower : ∃ e₁ : ℝ, 0 ≤ e₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ (M : Multiset ℤ) (y z : ℝ),
    1 < y → (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z →
    y * Rk k z * (1 - fSieve (log y / log z) / (log y / log z) -
      e₁ * log (log (3 * k)) / log y) < siftedCount k M z := by
  sorry

/-- **[I71, Theorem 2]**: `C₀(r) ≪ r² log² r`. If each of `m` consecutive integers
`x, x + 1, …, x + m - 1` is divisible by one of the first `r ≥ 2` primes, then
`m ≤ C r² log² r` for an absolute constant `C`. -/
theorem theorem2 : ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ (x : ℤ) (m : ℕ),
    (∀ k < m, ∃ i < r, (Nat.nth Nat.Prime i : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * r ^ 2 * log r ^ 2 := by
  sorry

/-- **[I71, Theorem 3]**, (1.5): under `(*)`, for `2 ≤ s < log y / (log log 3y)⁶`,
`|A_k(M; y^{1/s}) - y R_k(y^{1/s})| ≤ C y R_k(y^{1/s}) (e/(s log s))^s`. -/
theorem theorem3_fst : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (M : Multiset ℤ) (y s : ℝ), 1 < y →
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ s →
    s < log y / log (log (3 * y)) ^ 6 →
    |(siftedCount k M (y ^ (1 / s)) : ℝ) - y * Rk k (y ^ (1 / s))| ≤
      C * y * Rk k (y ^ (1 / s)) * (exp 1 / (s * log s)) ^ s := by
  sorry

/-- **[I71, Theorem 3]**, (1.6): under `(*)`, for `z ≥ 2` with
`log z < log y log log log 16y / (2 log log 3y)`,
`|A_k(M; z) - y R_k(z)| ≤ C y R_k(z) / log y`. -/
theorem theorem3_snd : ∃ C : ℝ, ∀ (k : ℕ) (M : Multiset ℤ) (y z : ℝ), 1 < y →
    (∀ d : ℕ, d.Coprime k → |(multiplesCount M d : ℝ) - y / d| ≤ 1) → 2 ≤ z →
    log z < log y * log (log (log (16 * y))) / (2 * log (log (3 * y))) →
    |(siftedCount k M z : ℝ) - y * Rk k z| ≤ C * y * Rk k z / log y := by
  sorry

end IwaniecLinearSieve
