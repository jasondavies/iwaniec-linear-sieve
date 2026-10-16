# Iwaniec's linear sieve

A Lean 4 / Mathlib formalisation of Iwaniec's linear sieve at the sifting limit,

> H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30,

and of its application to Jacobsthal's problem,

> H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231,

whose Corollary is

> **Theorem** (Iwaniec, 1978). There is an absolute constant `C` such that if `m` consecutive
> integers are each divisible by one of `r ≥ 2` given primes, then `m ≤ C (r log r)²`.

```lean
theorem IwaniecLinearSieve.iwaniecBound :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2
```

It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and contains no
`sorry`. Build with `lake exe cache get && lake build`; then
`lake env lean scripts/CheckAxioms.lean` checks every declaration of the library and of the
vendored prime number theorem against that allowlist (CI runs both).

## Sources

* [I78] H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231
  ([doi:10.1515/dema-1978-0121](https://doi.org/10.1515/dema-1978-0121)): the shifted sieve
  (Lemma 1), the estimates quoted from [I71] (Lemma 2), the Theorem and its Corollary.
* [I71] H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30: the
  Rosser–Iwaniec linear sieve at the sifting limit, with an `O(1/log y)` error in the main term
  (Theorem 4) and support of size `O(y / log² y)` (Theorem 5).
* J. Friedlander, H. Iwaniec, *Opera de Cribro*, AMS (2010), §12.4–12.6, for the modern form of
  the same argument.

[I71] is formalised in full: §2 (Lemmas 1, 2 for general `k` and sequences), §3 (the functions
`f`, `F`, `𝔐`, `𝔚`, Lemmas 3–10, including Lemma 5 with `F(3) = 2e^γ - 3` and the asymptotics of
`𝔐`), §4 (Lemmas 11–17, Theorem 4: main term with error `O(1/log y)`; Theorem 5: support of size
`O(y / log² y)`) and §5 (Theorem 1 with its Corollary, Theorems 2 and 3), in the module
`IwaniecLinearSieve.Main`: `theorem1_full`, `corollary_upper`, `corollary_lower`, `theorem2`
(`C₀(r) ≪ r² log² r`), `theorem3_fst`, `theorem3_snd`. [I78] uses only the lower bound of
Theorem 1 at level `y = C₀ z²` (`linearSieveEstimate`), so `iwaniecBound` does not depend on §5 or
on the results involving `γ`.

[I78] is formalised in full: Lemma 1 for arbitrary sequences, multiplicative functions `f`, `g`
and weights, with both the lower bound (4) and the upper bound (3) (`shiftedSieve_lower`,
`shiftedSieve_upper`); Lemma 2 (`lemma2_sum_abs_le`, `lemma2_sum_sigma_ge`); the Theorem, that
every interval of length `c ∏ (1 - 1/q_i)⁻¹ r² log r` contains at least `r²` integers coprime to
`q₁ ⋯ q_r` (`iwaniec_theorem`); and the Corollary deduced from it (`iwaniec_corollary`).
`iwaniecBound` proves the Corollary directly from the special case of Lemma 1 for intervals
(`shiftedSieve`), and the module `IwaniecLinearSieve.Jacobsthal` imports only what it needs (not
§5, `EulerGamma`, `General`, or the asymptotics of `𝔐` and the Dickman function).

`BLUEPRINT.md` maps each lemma to its Lean statement and records every deviation; the most
notable are listed below.

## Prime number theorem

At the sifting limit the main term is only of size `1/log z`, so the prime sums must be known
with relative error `o(1/log x)` uniformly over all scales; this needs PNT-strength input
(see `BLUEPRINT.md`). We use the de la Vallée Poussin form
`ψ(x) = x + O(x exp(-c √log x))` (`StrongPNT`) from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), whose
15-file import closure is vendored in `vendor/strong-pnt` (Apache 2.0) and ported to
Lean 4.35.0, together with its `IEANTN/Mertens.lean` (Mertens' theorems with the constant
`e^{-γ}`); `vendor/strong-pnt/UPSTREAM.json` records the revision, file hashes and the six
local patches. The vendored modules live under the prefix `IwaniecLinearSieveVendor`, so a
project can depend on both this library and PrimeNumberTheoremAnd; since the declarations keep
their upstream names, a single file should not import both.

## Layout

| Module | Content |
|---|---|
| `PrimeSums` | `Σ 1/p`, `∏ (1 - 1/p)` with PNT errors; [I71, Lemmas 13, 14]; `p_r ≪ r log r` |
| `Rosser` | Rosser's sieve: supports `D^±`, sieve property, deficits, support recursions ([I71, §2]) |
| `SieveFunctions` | `g_n`, `f`, `F`, `f(2) = 2` ([I71, §3, Lemmas 3–5]) |
| `SieveMajorants` | `𝔐`, `𝔚`, `𝔣`, `𝔉` ([I71, §3, Lemmas 6, 8–10]); the asymptotics of `𝔐` (Theorem 1); the Dickman function |
| `LinearSieve` | [I71, §4]: Lemmas 7, 11, 12, Corollaries, crude bounds, Theorems 4, 5, and `linearSieveEstimate` |
| `General` | [I71, §2] for general `k` and sequences: `A_k(M; z)`, `R_k`, Lemma 1 with arbitrary truncations and its Corollary, Lemma 2, (2.12), (2.13); `k/φ(k) ≪ log log 3k`; Lemma 16 |
| `Main` | [I71, §1, §5]: Theorems 1–3 and the Corollary; a fundamental lemma for small `z` |
| `Jacobsthal` | [I78]: the shifted sieve for intervals, the reduction, and `iwaniecBound`; `Jacobsthal.LemmaOne`, `.LemmaTwo`, `.Theorem`: Lemmas 1, 2, the Theorem and the Corollary as stated |
| `EulerGamma` | Euler's constant: `R(z) log z → e^{-γ}`, Buchstab's `ω` and `ω(∞) = e^{-γ}`, [I71, Lemma 5] in full (`F(3) = 2e^γ - 3`), Theorem 4 with `e^γ` |

## Deviations from the papers

* The core estimates (Theorems 4 and 5, [I71, §§3–4]) are for `k = 1`, as in [I71]'s proof;
  general `k` and sequences enter through §2 (`General`, via (2.12), (2.13)) and §5 (`Main`).
* The error `exp(-√log x)` in [I71] is `exp(-κ √log x)` for a fixed `κ > 0` from the PNT.
* The main chain (`theorem4`, `iwaniecBound`) works with the limit `cR` of `R(z) log z` in
  place of the Mertens constant `e^{-γ}` (it cancels), and uses from [I71, Lemma 5] only
  `f(2) = 2` and `F(3) ≥ 0`, which gives `1 - f(s)/s ≥ 3 log(s-1)/s`. The parts involving `γ`
  are proved separately in `EulerGamma`: `cR = e^{-γ}` (Mertens' third theorem, from
  PrimeNumberTheoremAnd), `theorem4_exp` (Theorem 4 with `e^γ`), and Lemma 5 in full, with
  Buchstab's limit `ω(∞) = e^{-γ}` (quoted by [I71] from Jurkat–Richert) proved via the Laplace
  transform of `ω` and `γ = -∫₀^∞ e^{-t} log t dt`; the convergence of `ω` comes from Iwaniec's
  identity `ω = w = (2s - W(s))/(s(3 + F(3)))` and the decay of `W = f - F`.
* [I71, Lemma 5] prints `F(s) = s - 6 + 2e^γ (1 - ∫_1^{s-2} log x/(x+1) dx)` on `[3, 5]`; the
  correct formula, which we prove, is `F(s) = 2e^γ (1 + ∫_1^{s-2} log x/(x+1) dx) - s` (the two
  agree at `s = 3`, but `F` is decreasing).
* [I71, Theorem 1 and Lemma 9] quote the asymptotics of the Dickman function `ϱ` from Hua's book
  and deduce those of `𝔐` from `𝔐(s+2) ≪ ϱ(s) ≪ 𝔐(s)`. We instead prove the asymptotics of `𝔐`
  (`bigM_asymp`) and Lemma 9 directly from (3.12), by comparison with the explicit sub- and
  supersolutions `exp(-Φ₁)`, `exp(-Φ₋₅)`, `Φ_c(s) = s(log s + log log s - 1 + (log log s + c)/log s)`;
  we then define `ϱ`, prove Iwaniec's two comparisons, and deduce de Bruijn's asymptotics of `ϱ`
  (`dickman_asymp`) from those of `𝔐`.
* Theorems 1–3 ([I71, §5]): the error terms need no `log log 3k` (since `R ≤ R_k`, so
  `1/R_k ≤ 1/R`), although `theorem1` and the Corollary are stated with it as printed. Theorem 1
  holds for `s ≤ ξ(y)`; the Corollary and (1.6) also need `z ≤ y^{1/ξ(y)}`, which [I71] does
  not treat: there we prove a fundamental lemma from the crude bounds at a lower sieve level.
  (1.3) is stated for `2 ≤ z ≤ y` with `F(s) + (3 - s)⁺` (our `F` is constant below 3), (1.4)
  for all `z ≥ 2`, (1.5) for `s ≥ 2`. Theorem 2 sifts by `z > P_r` rather than `z = P_r`.
* Several small gaps in [I71] are filled (e.g. Lemma 10 assumes, without proof, that
  `𝔐(t-1)/𝔐(t)` increases; the monotonicity used in Corollary 3 does not follow from Lemma 12;
  the slack in Theorem 4's induction must be `(log L)²/L²` rather than `1/L²`); see
  `BLUEPRINT.md`.
* [I78, Lemma 1] prints the conditions with the inequality signs interchanged: `(+) σ_m ≤ Σ μ(n)`
  for the upper bound (3) and `(−) σ_m ≥ Σ μ(n)` for the lower bound (4). The proof of (4), and
  its application to Rosser's lower-bound weights, need `σ_m ≤ Σ_{n ∣ m} μ(n)`.
* [I78, Lemma 2] quotes (6) from [I71] as an asymptotic equality, but [I71] proves only the
  lower bound (Theorem 4 bounds the deficit from above only). We prove the lower bound
  (`lemma2_sum_sigma_ge`), which is all the proof of the Theorem uses, and the trivial upper
  bound `≤ 1`.
* [I78, §3] takes `z = p_r`; the last step, `y / log² z > r²`, needs Chebyshev's bound
  `π(z) ≪ z / log z`, and Lemma 2 needs `z` large. We reduce small `r` to `N₀ r` primes by
  adding primes larger than `2 N₀ r`.
