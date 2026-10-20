module

public import IwaniecLinearSieve.Main.TheoremOne
public import IwaniecLinearSieve.EulerGamma
public import IwaniecLinearSieve.SieveMajorants

@[expose] public section

/-!
# [I71, Theorem 1] with the properties of `f`, `F`, `𝔐`

[I71, Theorem 1] states the bounds (1.1), (1.2) "where `f(s)`, `F(s)`, `𝔐(s)` are defined in §3
and satisfy" explicit formulas. This file bundles `theorem1` with those formulas:
`fSieve_eq_of_mem_Icc` and `FSieve_eq_of_mem_Icc` ([I71, Lemma 5]; the printed formula for `F`
has a sign slip, see `FSieve_eq_of_mem_Icc`) and `bigM_asymp`.
-/

open Real

namespace IwaniecLinearSieve

/-- **[I71, Theorem 1]**, with the formulas for `f`, `F` and `𝔐` stated there. -/
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
      s * (log s + log (log s) - 1 + log (log s) / log s)| ≤ C * s / log s) :=
  ⟨theorem1, fun _ hs => fSieve_eq_of_mem_Icc hs, fun _ hs => FSieve_eq_of_mem_Icc hs,
    bigM_asymp⟩

end IwaniecLinearSieve
