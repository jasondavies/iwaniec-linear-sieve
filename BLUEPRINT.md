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

## Module specifications

Conventions: everything lives in `namespace IwaniecJacobsthal`; `primesLT`, `primorialLT`, `R`
are in `IwaniecJacobsthal/Basic.lean`. Statements below are targets; names and exact forms may
be adjusted when that makes them easier to use, provided the mathematical content is kept and
this file is updated. No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.

### A. `IwaniecJacobsthal/PrimeSums.lean` — prime sums from `StrongPNT`

Iwaniec uses "the well known formula" `S(x) = Σ_{p≤x} 1/p = log log x + c₅ + O(exp(-√log x))`
and `R(z) = e^{-γ}/log z + O(exp(-√log z))`. The PNT gives these with `exp(-κ √log x)` for some
fixed `κ > 0`; we use one fixed `κ` everywhere.

* `pntκ : ℝ`, `pntκ_pos : 0 < pntκ`, `pntE (x : ℝ) : ℝ := exp (-pntκ * √(log x))`.
* `S (x : ℝ) : ℝ := ∑ p ∈ primesLT (⌊x⌋₊ + 1), (p : ℝ)⁻¹` (primes `p ≤ x`).
* `S_asymp : ∃ c₅ C, ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x`.
* `R_asymp : ∃ cR > 0, ∃ C, ∀ z ≥ 2, |R z * log z - cR| ≤ C * pntE z`
  (any constant `cR`; its value `e^{-γ}` is not needed).
* [I71, Lemma 13] for `b ≥ 0` monotone on `[B, A]`, `2 ≤ B ≤ A`:
  `|∑_{B ≤ p ≤ A} b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B`,
  and the antitone version with `b B` in place of `b A`.
* `nth_prime_le : ∃ C, ∀ r ≥ 2, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r`
  (the `r`-th prime is `≪ r log r`).

### B. `IwaniecJacobsthal/Rosser.lean`, `ShiftedSieve.lean`, `Jacobsthal.lean` (done)

Rosser's β = 2 linear sieve [I71, §2] in recursive form. With `lower = true` for `D⁻` (conditions
at even indices) and `false` for `D⁺` (odd indices), `rosserPrimes lower y z` is the set of primes
`p < z` with `lower ∨ p³ < y`, and

    rosserSet lower y z = {1} ∪ ⋃_{p ∈ rosserPrimes lower y z} p • rosserSet (!lower) (y/p) p

(well founded on `⌈z⌉₊`; unfolding lemma `rosserSet_eq`, induction principle
`primesLT_induction`). Equivalently `d = p₁⋯p_l`, `p₁ > ⋯ > p_l`, `p₁ < z`, and
`p₁⋯p_m p_m² < y` for every `m ≤ l` of the right parity. Proved (`Rosser.lean`):

* `squarefree_of_mem_rosserSet`, `primeFactors_subset_of_mem_rosserSet`,
  `dvd_primorialLT_of_mem_rosserSet`;
* `sum_rosserSet`: `∑_{d ∈ D} f d = f 1 + ∑_{p ∈ rosserPrimes} ∑_{d ∈ rosserSet (!lower) (y/p) p} f (p d)`;
* sieve property for every `m : ℕ` (`rosserSieve_le_siftIndicator_le`,
  `sum_moebius_rosserSet_true_le`, `le_sum_moebius_rosserSet_false`):
  `∑_{d ∈ D⁻, d ∣ m} μ d ≤ [no p < z divides m] ≤ ∑_{d ∈ D⁺, d ∣ m} μ d`, via Buchstab's identity
  `siftIndicator_eq`; for `m ∣ primorialLT z` the middle term is `[m = 1]`
  (`rosserSieve_of_dvd_primorialLT`);
* `R_eq : R z = 1 - ∑_{p < z} R p / p` ([I71, (2.11)]), `R_pos`, `R_nonneg`;
* `rosserMain lower y z = ∑_{d ∈ rosserSet lower y z} μ d / d`, with
  `rosserMain_eq : rosserMain lower y z = 1 - ∑_{p ∈ rosserPrimes} rosserMain (!lower) (y/p) p / p`;
* `fail : Bool → ℕ → ℝ → ℝ → ℝ` exactly as below, `fail_nonneg`, `fail_mono` (monotone in `r`), and
  for `#(primesLT z) < r` (`fail_eq_of_card_lt`, `rosserMain_true_eq`, `rosserMain_false_eq`):
  `R z - rosserMain true y z = fail true r y z`, `rosserMain false y z - R z = fail false r y z`;
  hence `rosserMain true y z ≤ R z ≤ rosserMain false y z`:

      fail _     0     y z = 0
      fail true  (r+1) y z = ∑_{p < z} fail false r (y/p) p / p
      fail false (r+1) y z = ∑_{p < z, p³ < y} fail true r (y/p) p / p + ∑_{p < z, ¬ p³ < y} R p / p

* counts: `card_rosserSet : #(rosserSet lower y z) = 1 + ∑_{p ∈ rosserPrimes} #(rosserSet (!lower) (y/p) p)`;
  depth-truncated ([I71, Lemma 17]), counting elements with at most `n` prime factors:
  `card_filter_rosserSet_zero` (`= 1` for `n = 0`) and `card_filter_rosserSet_succ`
  (`#{d ∈ D : ω(d) ≤ n+1} = 1 + ∑_{p ∈ rosserPrimes} #{d ∈ rosserSet (!lower) (y/p) p : ω(d) ≤ n}`).

`ShiftedSieve.lean`: [I78, Lemma 1] for intervals (`shiftedSieve`): for primes `S` with
`#S = #(primesLT z)`, any `y`, `x : ℤ`, `X : ℕ`,

    X * ∏_{q ∈ S} (1 - q⁻¹) * (rosserMain true y z / R z) - #(rosserSet true y z)
      ≤ #{k ∈ range X | ∀ q ∈ S, ¬ (q:ℤ) ∣ x + k}

(from `shiftedSieve_of_bijOn`, for any bijection `e : primesLT z → S` with `p ≤ e p`; the
order-preserving one has this property, `exists_bijOn_primesLT_le`). Divisors of squarefree
numbers are handled as sets of primes; the algebra is `sum_powerset_div_prod` (Möbius inversion
`∑_A w(A)/∏_A g = ∏(1 - 1/g) ∑_B σ(B)/∏_B (g-1)`) and `prod_mul_sum_div_le_sum`. Also
`R_le_prod_of_card_eq : R z ≤ ∏_{q ∈ S} (1 - q⁻¹)`.

`Jacobsthal.lean`: the final assembly `iwaniecBound_of_estimates`: from

    LinearSieveEstimate : ∃ C₀ c K z₀ : ℝ, 0 < c ∧ ∀ z ≥ z₀,
      R z - rosserMain true (C₀ * z^2) z ≤ R z * (1 - c / log z) ∧
      #(rosserSet true (C₀ * z^2) z) ≤ K * z^2 / (log z)^2

(this is [I78, Lemma 2]: (6) says `rosserMain true y z / R z = ∑ σₙ/φ(n) ≥ c / log z` once `C₀` is
large, and (5) says `∑|λₙ| = #D⁻ ≪ y / log² y`, for `z ≥ z₀(C₀)`), together with
`∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z` (from `R_asymp`) and
`∃ C, ∀ r ≥ 2, (Nat.nth Nat.Prime (r-1) : ℝ) ≤ C * r * log r` (`nth_prime_le`), it derives

    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2

(this is `ShiftedGcd.IwaniecBound`). Intermediate step `exists_covering_length_le`: for
`z ≥ z₁` and `#S = #(primesLT z)`, a covered run has length `m ≤ K z²`. Small `r` is handled
without a separate argument: `S` (with `#S = r`) is enlarged to `N = N₀ r` primes
(`exists_superset_card_eq`), where `N₀ = ⌈z₁⌉₊ + 2`, and `z = p_N + 1` (so `primesLT z` is the
first `N` primes, `card_primesLT_nth_prime_add_one`, and `z ≥ z₁`); then
`p_N ≪ N log N ≪_{N₀} r log r`.

### C1. `IwaniecJacobsthal/SieveFunctions.lean` — [I71, §3] `g_n`, `f`, `F`

Real functions on `ℝ` (values outside the stated domains are irrelevant but should be chosen so
that the stated identities hold, e.g. odd `g` constant on `s ≤ 3`):

* `g : ℕ → ℝ → ℝ` for `n ≥ 2` with (3.1)–(3.3):
  `g 2 s = 3 log(3/(s-1)) + s - 4` on `[2,4]`, `0` for `s ≥ 4`;
  `g (2n+1) s = ∫_s^∞ g (2n) (t-1)/(t-1) dt` for `s ≥ 3`, `= g (2n+1) 3` for `1 ≤ s ≤ 3`;
  `g (2n+2) s = ∫_s^∞ g (2n+1) (t-1)/(t-1) dt` for `s ≥ 2` (`n ≥ 1`).
  Continuous, nonnegative, antitone on their domains, `g i s = 0` for `s ≥ 2 + i`.
* Lemmas 3, 4 ((3.4), (3.5) with `A = (1 + 3 log 3)/6 < 0.72`).
* `f s = ∑' i ≥ 1, g (2i) s` (`s ≥ 2`), `F s = ∑' i ≥ 1, g (2i+1) s` (`s ≥ 1`); convergence,
  continuity, (3.6), (3.7), `0 < f s`, `f s, F s = O(s e^{-s})`.
* Lemma 5 (the part needed): `f 2 = 2` and (3.9)
  `f s = f 4 + (F 3 + 3) log(3/(s-1)) + s - 4` for `2 ≤ s ≤ 4`; hence
  `1 - f s / s ≥ 3 log(s - 1) / s` on `[2, 4]` (using `F 3 ≥ 0`).
* `fr r s` = `f` (r even) / `F` (r odd) as in [I71] before Lemma 7, and partial sums as needed
  by [I71, §4].

### C2. `IwaniecJacobsthal/SieveMajorants.lean` — [I71, §3] `𝔐`, `𝔚`, `𝔣`, `𝔉`

* `𝔐`, `𝔚` (Lean names e.g. `bigM`, `bigW`) as the continuous solutions of the delay
  equations in [I71, §3, Definition]; (3.11), (3.12); `0 < 𝔐`, `𝔐` antitone, `𝔐 = O(e^{-s})`;
  `𝔣 = (𝔐 + 𝔚)/2`, `𝔉 = (𝔐 - 𝔚)/2`, their explicit values on `[1,3]`/`[2,3]`, (3.13),
  (3.14); Lemma 6 and its corollary; `G r` = `𝔣` (r even) / `𝔉` (r odd); Lemma 8; Lemma 10 and
  its corollary.
* Lemma 9, lower bound only: `G r s ≥ exp(-s log s - s log log s - c s)` for `s ≥ 3`.
  [I71] quotes de Bruijn-type asymptotics of the Dickman function from Hua's book; instead use
  a comparison principle for (3.12) with an explicit subsolution
  `h(s) = exp(-(s log s + s log log s + C s))` (convexity of the exponent gives
  `∫_{s-1}^s h ≥ h(s-1)(1 - e^{-h'})/h'`).
* Lemma 7 (`f_r < M ≤ 4𝔐`) needs `M = f + F` from C1; state it after both are merged.

### D. `IwaniecJacobsthal/MainTerm.lean`, `Remainder.lean`, `LinearSieve.lean` — [I71, §4–5]

Lemmas 11, 12, Corollaries 1–3 to Lemma 13, Lemmas 14–17, Theorems 4 and 5, and from them
`LinearSieveEstimate`.
