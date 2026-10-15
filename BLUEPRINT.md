# Blueprint

Goal: a Lean 4 / Mathlib proof of

> **Iwaniec (1978).** There is an absolute constant `C` such that for any primes
> `q₁ < … < q_r`, `r ≥ 2`, every interval of `C·(r log r)²` consecutive integers contains an
> integer coprime to `q₁⋯q_r`.

following

* [I71] H. Iwaniec, *On the error term in the linear sieve*, Acta Arith. 19 (1971), 1–30;
* [I78] H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978), 225–231.

[I71] is followed lemma by lemma, specialised to `k = 1` (the only case [I78] uses). The
prime-number input is the de la Vallée Poussin prime number theorem
`ψ(x) = x + O(x exp(-c √log x))`, taken from PrimeNumberTheoremAnd (`StrongPNT`, vendored in
`vendor/strong-pnt`).

## Layers

| Layer | Content | Lean module |
|---|---|---|
| PNT | `StrongPNT` (vendored) | `PrimeNumberTheoremAnd.StrongPNT` |
| Prime sums | `S(x) = Σ_{p≤x} 1/p = log log x + c₅ + O(exp(-√log x))`; `R(z) = Π_{p<z}(1-1/p)` with `R(z) log z → e^{-γ}`-type estimate `R(z) = c_R / log z + O(exp(-√log z))`; [I71, Lemma 13, Corollaries 1–3, Lemma 14] | `IwaniecJacobsthal.PrimeSums` |
| Sieve combinatorics | [I71, §2]: Lemma 1 (the inequalities (2.1), (2.2)), its corollary (2.5)–(2.8), Lemma 2 (`G = S`, `D = T`), the identities (2.14), (2.15) | `IwaniecJacobsthal.Rosser` |
| Sieve functions | [I71, §3]: `g_n`, `f`, `F`, Lemmas 3–10, `𝔐`, `𝔚`, `𝔣`, `𝔉`, `f(2) = 2` | `IwaniecJacobsthal.SieveFunctions` |
| Estimates | [I71, §4]: Lemmas 11–17, Theorems 4, 5 | `IwaniecJacobsthal.MainTerm`, `IwaniecJacobsthal.Remainder` |
| Linear sieve | [I71, §5]: Theorem 1 lower bound (1.2)/(1.4), as needed by [I78, Lemma 2] | `IwaniecJacobsthal.LinearSieve` |
| Jacobsthal | [I78]: Lemma 1 (shifted sieve), Theorem, Corollary | `IwaniecJacobsthal.ShiftedSieve`, `IwaniecJacobsthal.Jacobsthal` |

## Deviations from the papers

* `k = 1` throughout [I71].
* [I78] needs from (6) only the lower bound
  `Σ σₙ / Π(p-1) ≥ 2e^γ … `; it is used only to make the main term `≫ (s-2)` for
  `s = 2 + O(1/log z)`. The exact value `F(3) = 2e^γ - 3` in [I71, Lemma 5] rests on the
  Buchstab limit `ω(∞) = e^{-γ}` quoted from Jurkat–Richert. We prove `f(2) = 2` and formula
  (3.9) exactly as in [I71], and use only `F(3) ≥ 0`, which gives
  `1 - f(s)/s ≥ 3 log(s-1)/s` on `2 ≤ s ≤ 4`. This suffices for [I78].

## Why PNT-strength prime sums

At the sifting limit the main term is only `≍ (s-2) ≍ 1/log z`, so it must be computed to
relative precision `O(1/log y)`. The β-sieve recursion reaches primes of every size: the
error-propagation operator of [I71, §4] has the positive fixed point `𝔐` (spectral radius 1),
so a relative error `ε(p)` in prime sums at scale `p ≈ z^{1/t}` contributes about
`ε(p)·t/log z` per dyadic range of `t`. Elementary Mertens (`ε(p) ≍ 1/log p`) therefore gives
total error `≍ log log z / log z`, which is too large; any improvement over `O(1/log x)` in
Mertens' second theorem is PNT-strength. [I71] uses `exp(-√log x)` errors.
