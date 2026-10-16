# Iwaniec's linear sieve

A Lean 4 / Mathlib formalisation of Iwaniec's linear sieve at the sifting limit,

> H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30,

with its application to Jacobsthal's problem,

> **Theorem** (H. Iwaniec, *On the problem of Jacobsthal*, 1978). There is an absolute
> constant `C` such that if `m` consecutive integers are each divisible by one of `r ≥ 2` given
> primes, then `m ≤ C (r log r)²`.

```lean
theorem IwaniecLinearSieve.iwaniecBound :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2
```

It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and contains no
`sorry`. Build with `lake exe cache get && lake build`.

## Sources

* [I78] H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231
  ([doi:10.1515/dema-1978-0121](https://doi.org/10.1515/dema-1978-0121)): the shifted sieve
  (Lemma 1) and the deduction of the theorem.
* [I71] H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30: the
  Rosser–Iwaniec linear sieve at the sifting limit, with an `O(1/log y)` error in the main term
  (Theorem 4) and support of size `O(y / log² y)` (Theorem 5).
* J. Friedlander, H. Iwaniec, *Opera de Cribro*, AMS (2010), §12.4–12.6, for the modern form of
  the same argument.

The proof follows [I71] lemma by lemma (with `k = 1`); `BLUEPRINT.md` maps each lemma to its
Lean statement and records every deviation. From [I71] we formalise §§2–4 in full: Rosser's
sieve, the functions of §3, Theorem 4 (main term with error `O(1/log y)`) and Theorem 5 (support
of size `O(y/log² y)`). Theorems 1–3, which package these for general sequences and `k`, are
formalised only in the case [I78] needs: the lower bound of Theorem 1 at level `y = C₀ z²`
(`linearSieveEstimate`).

## Prime number theorem

At the sifting limit the main term is only of size `1/log z`, so the prime sums must be known
with relative error `o(1/log x)` uniformly over all scales; this needs PNT-strength input
(see `BLUEPRINT.md`). We use the de la Vallée Poussin form
`ψ(x) = x + O(x exp(-c √log x))` (`StrongPNT`) from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), whose
15-file import closure is vendored in `vendor/strong-pnt` (Apache 2.0) and ported to
Lean 4.35.0; `vendor/strong-pnt/UPSTREAM.json` records the revision, file hashes and the four
local patches.

## Layout

| Module | Content |
|---|---|
| `PrimeSums` | `Σ 1/p`, `∏ (1 - 1/p)` with PNT errors; [I71, Lemmas 13, 14]; `p_r ≪ r log r` |
| `Rosser` | Rosser's sieve: supports `D^±`, sieve property, deficits, support recursions ([I71, §2]) |
| `SieveFunctions` | `g_n`, `f`, `F`, `f(2) = 2` ([I71, §3, Lemmas 3–5]) |
| `SieveMajorants` | `𝔐`, `𝔚`, `𝔣`, `𝔉` ([I71, §3, Lemmas 6, 8–10]); the asymptotics of `𝔐` (Theorem 1); the Dickman function |
| `LinearSieve` | [I71, §4]: Lemmas 7, 11, 12, Corollaries, crude bounds, Theorems 4, 5, and `linearSieveEstimate` |
| `Jacobsthal` | [I78]: the shifted sieve (Lemma 1), the reduction, and `iwaniecBound` |

## Deviations from the papers

* `k = 1` throughout [I71].
* The error `exp(-√log x)` in [I71] is `exp(-κ √log x)` for a fixed `κ > 0` from the PNT.
* The Mertens constant `e^{-γ}` is replaced by the (unspecified) limit `cR` of `R(z) log z`;
  it cancels. The values `F(3) = 2e^γ - 3` and `f(s) = s - 2e^γ log(s-1)` are not needed: we
  prove `f(2) = 2` and use only `F(3) ≥ 0`, which gives `1 - f(s)/s ≥ 3 log(s-1)/s`.
* [I71, Theorem 1 and Lemma 9] quote the asymptotics of the Dickman function `ϱ` from Hua's book
  and deduce those of `𝔐` from `𝔐(s+2) ≪ ϱ(s) ≪ 𝔐(s)`. We instead prove the asymptotics of `𝔐`
  (`bigM_asymp`) and Lemma 9 directly from (3.12), by comparison with the explicit sub- and
  supersolutions `exp(-Φ₁)`, `exp(-Φ₋₅)`, `Φ_c(s) = s(log s + log log s - 1 + (log log s + c)/log s)`;
  we then define `ϱ`, prove Iwaniec's two comparisons, and deduce de Bruijn's asymptotics of `ϱ`
  (`dickman_asymp`) from those of `𝔐`.
* Several small gaps in [I71] are filled (e.g. Lemma 10 assumes, without proof, that
  `𝔐(t-1)/𝔐(t)` increases; the monotonicity used in Corollary 3 does not follow from Lemma 12;
  the slack in Theorem 4's induction must be `(log L)²/L²` rather than `1/L²`); see
  `BLUEPRINT.md`.
