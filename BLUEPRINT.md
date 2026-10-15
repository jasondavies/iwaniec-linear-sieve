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
  `pntκ = min c (1/2)` with `c` from `StrongPNT`; facts `pntE_pos`, `pntE_le_one`,
  `pntE_le_pntE` (antitone on `x > 0`), `pntE_antitoneOn_Ici_one`, `tendsto_pntE`,
  `inv_le_pntE : 2 ≤ x → x⁻¹ ≤ pntE x`, `one_div_mul_log_le_pntE : 1/(x log x) ≤ 2 pntE x`,
  `sqrt_mul_log_le : 1 ≤ x → √x log x ≤ 12 x pntE x`.
* `theta_asymp : ∃ C, 0 ≤ C ∧ ∀ x ≥ 2, |θ x - x| ≤ C * x * pntE x` (`Chebyshev.theta`).
* `S (x : ℝ) : ℝ := ∑ p ∈ primesLT (⌊x⌋₊ + 1), (p : ℝ)⁻¹` (primes `p ≤ x`).
* `S_asymp : ∃ c₅ C, ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x`.
* `R_asymp : ∃ cR > 0, ∃ C, ∀ z ≥ 2, |R z * log z - cR| ≤ C * pntE z`
  (any constant `cR`; its value `e^{-γ}` is not needed);
  `R_lower : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z`, `R_upper : ∃ C > 0, ∀ z ≥ 2, R z ≤ C / log z`,
  `R_pos`, `R_antitone`.
* [I71, Lemma 13] for `b ≥ 0` monotone on `[B, A]`, `2 ≤ B ≤ A`, with
  `primesIcc B A = {p ∈ Icc ⌈B⌉₊ ⌊A⌋₊ | p.Prime}` (`mem_primesIcc : p ∈ primesIcc B A ↔
  p.Prime ∧ B ≤ p ∧ p ≤ A`):
  `lemma13_mono : ∃ C, ∀ b A B, 2 ≤ B → B ≤ A → MonotoneOn b (Icc B A) → (∀ x ∈ Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIcc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B`,
  and `lemma13_anti` (`AntitoneOn`, `b B` in place of `b A`). The variants
  `lemma13_mono_of_subset`, `lemma13_anti_of_subset` hold for any `s : Finset ℕ` lying between
  the primes in `(B, A)` and those in `[B, A]`, so any choice of strict/non-strict endpoints works
  (also `primesIoc`, `primesIoo` with `mem_` lemmas).
* [I71, Lemma 14]: `lemma14 : ∃ C, ∀ A B, 2 ≤ B → B ≤ A →
    |∑ p ∈ primesIoo B A, 1 / (p * log p) - (1 / log B - 1 / log A)| ≤ C * pntE B`
  (and `lemma14_of_subset`).
* `nth_prime_le : ∃ C, ∀ r ≥ 2, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r`
  (the `r`-th prime is `≪ r log r`).

Files: `PrimeSums/Error.lean` (`pntE`, `theta_asymp`), `Mertens.lean` (`S_asymp`, by Abel
summation against `θ`), `Product.lean` (`R`), `SummationByParts.lean` (abstract discrete
summation by parts), `Lemma13.lean` (Lemmas 13, 14), `NthPrime.lean`.

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

### C1. `IwaniecJacobsthal/SieveFunctions.lean` — [I71, §3] `g_n`, `f`, `F` (done)

Files: `SieveFunctions/Defs.lean` (`g`), `Bounds.lean` (Lemmas 3, 4), `Series.lean` (`f`, `F`,
Corollary to Lemma 4), `LemmaFive.lean` (`M`, `f(2) = 2`); `SieveFunctions.lean` imports all four.

* `g : ℕ → ℝ → ℝ` is defined on all of `ℝ` by clamping: `g 0 = g 1 = 0`;
  `g 2 s = gTwoFormula (max 2 (min s 4))` with `gTwoFormula s = 3 log(3/(s-1)) + s - 4`;
  `g (n+3) s = ∫ t in max s (gLower (n+3))..(n+5), shiftKernel (g (n+2)) t`, where
  `gLower i = 2` (even `i`) / `3` (odd `i`) and `shiftKernel h t = h (t-1) / max (t-1) 1`.
  Identities: `g_two_eq` (`s ∈ Icc 2 4`), `g_two_of_four_le`; `g_odd_eq_integral`
  (`1 ≤ n`, `3 ≤ s`: integrable on `Ioi s` and `g (2n+1) s = ∫ t in Ioi s, g (2n) (t-1)/(t-1)`),
  `g_odd_of_le_three` (`s ≤ 3 → g (2n+1) s = g (2n+1) 3`), `g_even_eq_integral` (`1 ≤ n`,
  `2 ≤ s`), `g_even_of_le_two`, `g_add_three_eq` (finite upper limit `n + 5`).
  Global properties (all `s : ℝ`): `continuous_g`, `g_nonneg`, `g_antitone`,
  `g_eq_zero_of_le : (i:ℝ) + 2 ≤ s → g i s = 0`, `g_pos : 2 ≤ i → s < i + 2 → 0 < g i s`.
* Lemma 3: `psi s = s⁻¹ * exp (s - 3) * (1 + 3 * log (3 / (s - 1)))`,
  `psi_le_psi_two : s ∈ Icc 2 4 → psi s ≤ psi 2`, `psi_two`.
* Lemma 4: `gLead = sSup ((fun s => g 2 s * s⁻¹ * exp s) '' Icc 2 4)` (`a`),
  `gRatio = (1 + 3 log 3)/6` (`A`), `gRatio_eq : gRatio = exp 1 / 3 * psi 2`,
  `gRatio_lt : gRatio < 0.72`, `gRatio_pos`, `gLead_nonneg`;
  (3.4) `g_odd_le' : 1 ≤ n → 1 ≤ s → g (2n+1) s ≤ gLead * (exp 1 / 3) * gRatio^(n-1) * s * exp (-s)`
  (also `g_odd_le n : 1 ≤ s → g (2n+3) s ≤ gLead * (exp 1/3) * gRatio^n * s * exp (-s)`);
  (3.5) `g_even_le n : 2 ≤ s → g (2n+2) s ≤ gLead * gRatio^n * s * exp (-s)`;
  `g_even_eq_on_Icc : s ∈ Icc 2 4 → g (2n+4) s = g (2n+4) 4 + g (2n+3) 3 * log (3/(s-1))`.
* Corollary: `fSieve s = ∑' n, g (2n+2) s`, `FSieve s = ∑' n, g (2n+3) s` (summable for every
  `s`: `summable_g_even`, `summable_g_odd`, geometric majorants `g_even_le_uniform`,
  `g_odd_le_uniform`); `fr r = fSieve` (even `r`) / `FSieve` (odd `r`) (`fr_of_even`,
  `fr_of_odd`). `continuous_fSieve`, `continuous_FSieve`, `fSieve_pos`, `FSieve_pos`,
  `fSieve_antitone`, `FSieve_antitone`, `fSieve_of_le_two`, `FSieve_of_le_three` ((3.7) on
  `s ≤ 3`), `fSieve_le : 2 ≤ s → fSieve s ≤ gLead * (1 - gRatio)⁻¹ * s * exp (-s)`,
  `FSieve_le` (`1 ≤ s`, extra factor `exp 1 / 3`), `fSieve_isBigO`, `FSieve_isBigO`
  (`=O[atTop] fun s => s * exp (-s)`); (3.6) `fSieve_eq_integral : 2 ≤ s →
  fSieve s = (∫ t in Ioi s, FSieve (t-1)/(t-1)) + g 2 s` and (3.7) `FSieve_eq_integral : 3 ≤ s →
  FSieve s = ∫ t in Ioi s, fSieve (t-1)/(t-1)` (integrability: `integrableOn_FSieve_shift`,
  `integrableOn_fSieve_shift`). Partial sums: `sum_g_even_le_fSieve`, `sum_g_odd_le_FSieve`,
  `g_even_le_fSieve`, `g_odd_le_FSieve`; `hasSum_g : HasSum (fun k => g (k+2) s) (fSieve s + FSieve s)`.
* Lemma 5: (3.9) `fSieve_eq_on_Icc' : s ∈ Icc 2 4 →
  fSieve s = fSieve 4 + (FSieve 3 + 3) * log (3/(s-1)) + s - 4`; `fSieve_four_add :
  fSieve 4 + (FSieve 3 + 3) * log 3 = 4`; `fSieve_eq_on_Icc : s ∈ Icc 2 4 →
  fSieve s = s - (FSieve 3 + 3) * log (s - 1)`; (3.10) `fSieve_two : fSieve 2 = 2`;
  `le_one_sub_fSieve_div` and
  `one_sub_fSieve_div_ge : ∀ s ∈ Icc 2 4, 1 - fSieve s / s ≥ 3 * Real.log (s - 1) / s`.
  Derivatives: `hasDerivAt_FSieve` (`3 < s`), `hasDerivAt_fSieve_of_lt_four` (`2 < s < 4`),
  `hasDerivAt_fSieve_of_four_lt`.
* Iwaniec's `M` (for Lemma 7 / C2): `MSieve s = fSieve s + FSieve s + max (3 - s) 0`, i.e.
  `f + F` on `s ≥ 3` (`MSieve_of_three_le`) and `3 + F(3) - s + f(s)` on `s ≤ 3`
  (`MSieve_of_le_three`); `continuous_MSieve`, `MSieve_nonneg`, `MSieve_antitone`, `MSieve_le`,
  `hasSum_g_MSieve : 3 ≤ s → HasSum (fun k => g (k+2) s) (MSieve s)`,
  `fr_lt_MSieve : fr r s < MSieve s`, (3.8) `hasDerivAt_MSieve : 3 < s → s ≠ 4 →
  HasDerivAt MSieve (-(MSieve (s-1)/(s-1))) s`.
* Proof of `f(2) = 2`: `lemma5Q s = (s-1) * MSieve s - ∫ x in (s-1)..s, MSieve x` has derivative
  `0` on `(3,4) ∪ (4,∞)` (`hasDerivAt_lemma5Q`), so is constant on `[3, ∞)` (`lemma5Q_const`), and
  `|lemma5Q b| ≤ C b² e^{-b}` for `b ≥ 4`, so `lemma5Q_three : lemma5Q 3 = 0`;
  `integral_MSieve_two_three` evaluates `∫_2^3 M` explicitly.

### C2. `IwaniecJacobsthal/SieveMajorants.lean` — [I71, §3] `𝔐`, `𝔚`, `𝔣`, `𝔉` (done)

Files `IwaniecJacobsthal/SieveMajorants/{Delay,Defs,Properties,Majorants,Lemmas}.lean`.

* `Delay.sol k y₀`: continuous solution of `y = y₀` on `(-∞, 3]`, `y' = k(s) y(s-1)` for `s > 3`;
  `pos_of_first_crossing` (first-crossing principle used for all comparison arguments).
* `bigM` (`𝔐`), `bigW` (`𝔚`): continuous on `ℝ`, constant `3`, `1` on `(-∞, 2]`;
  `bigM_eq`, `bigW_eq` (values on `[2,3]`), `bigM_eq_integral`, `bigW_eq_integral` (`s ≥ 3`),
  `hasDerivAt_bigM`, `hasDerivAt_bigW` (`s > 3`).
* (3.11) `bigW_eq_neg_mul_integral : 3 ≤ s → bigW s = -s * ∫ x in (s-1)..s, bigW x / x^2`;
  (3.12) `bigM_integral_identity : 3 ≤ s →
  ((s-1)^2 - 1/2) * bigM s / s = ∫ x in (s-1)..s, (1 - 1/(2*x^2)) * bigM x`.
* `bigM_pos (s) : 0 < bigM s`, `bigM_antitone`, `bigM_le_three`,
  `bigM_le_exp (s) : bigM s ≤ 3 * exp 5 * exp (-s)`, `abs_bigW_le_exp`, `bigM_le_ratio`.
* Lemma 6: `abs_bigW_le (s) : |bigW s| ≤ bigM s / 3` (all `s`), strict for `s ≥ 3`
  (`abs_bigW_lt`).
* `majf` (`𝔣`), `majF` (`𝔉`), `majG r` (`G_r`); `majF_of_le_three` (`𝔉 = 1` on `s ≤ 3`),
  `majf_eq` (on `[2,3]`); Corollary to Lemma 6: `majf_mem`, `majF_mem`,
  `majG_mem (r s) : bigM s / 3 ≤ majG r s ∧ majG r s ≤ 2 * bigM s / 3`; `majG_pos`,
  `majG_le_two`, `continuous_majG`, `majG_antitone`.
* (3.13) `majF_eq_integral : 3 ≤ s → majF s = ∫ t in Ioi s, majf (t-1) * t / (t-1)^2`;
  (3.14) `majf_eq_integral : 2 ≤ s → majf s = ∫ t in Ioi s, majF (t-1) * t / (t-1)^2`.
* `hasDerivAt_majG_succ (r) : (5 + (-1)^r)/2 < t →
  HasDerivAt (majG (r+1)) (-(majG r (t-1) * t / (t-1)^2)) t` (for [I71, Lemmas 11, 12]).
* Lemma 8: `bigM_sub_one_lt : 3 ≤ s → bigM (s-1) < 4 * s^2 * bigM s` (`bigM_sub_one_div_lt`).
* Lemma 10: `log_mul_bigM_lt : 2 ≤ t → log t * bigM t < 2 * (t/(t-1)^2) * bigM (t-1)`,
  `bigM_mul_log_div_lt : 3 ≤ t → bigM t * t * log t / bigM (t-1) < 9/2`; Corollary:
  `majG_succ_mul_log_div_lt (r) : 2 ≤ t →
  majG (r+1) t * (t-1)^2 * log t / (majG r (t-1) * t) < 4` (so `c₃ = 4`, on the larger range
  `t ≥ 2` for every `r`). [I71]'s proof uses that `𝔐(t-1)/𝔐(t)` increases; we instead run a
  first-crossing argument on `log t 𝔐(t) < 2t/(t-1)² 𝔐(t-1)` (cf. Opera de Cribro, Lemma 11.7).
* Lemma 9, lower bound: `bigM_ge_exp : ∃ κ > 0, ∀ s ≥ 3,
  κ * exp (-(s * log s + s * log (log s) + 2 * s)) ≤ bigM s` and
  `majG_ge_exp : ∃ c, ∀ r s, 3 ≤ s → exp (-(s * log s) - s * log (log s) - c * s) ≤ majG r s`,
  by comparison with the subsolution `lemma9Fun` of (3.12).
* Lemma 7 (`f_r < M ≤ 4𝔐`) needs `M = f + F` from C1; state it after both are merged.

### D. [I71, §4–5]: from the sieve functions to `LinearSieveEstimate`

Files: `IwaniecJacobsthal/LinearSieve/*.lean`. Notation: `L = log y`,
`ξ(y) = L / (log log (3y))^{11/5}`, `δ(s, y) = (1 + s² (log s)⁵ / L²)^{5s}`, `z = y^{1/s}`,
`t_p = L / log p` (so the inner level `(y/p, p)` has parameter `t_p - 1`). Main-term
majorants `M true = fSieve`, `M false s = FSieve s + max (3 - s) 0` (`= MSieve s - fSieve s`);
error majorants `G true = 𝔣`, `G false = 𝔉`; domains `s ≥ 2` (true), `s ≥ 1` (false).
`cR` is the constant of `R_asymp`; it plays the role of Iwaniec's `e^{-γ}` and cancels in the end.

Our `fail false` also contains the depth-1 term `Σ_{y^{1/3} ≤ p < z} R(p)/p = R(y^{1/3}) - R(z)`
(Iwaniec's `Q_{odd}` starts at depth 3 and his `d_{2,y}` is handled by Lemma 16). Correspondingly
`M false` contains `(3 - s)⁺`, and `fSieve s = ∫_s^∞ M false (t-1)/(t-1) dt` for `s ≥ 2` follows
from (3.6) and `g 2 s = ∫_s^∞ (4 - t)⁺/(t-1) dt`. This replaces Lemmas 14 and 16 by the
telescoping identity and `R_asymp`.

Items 1–4 are done, in `LinearSieve/Calculus.lean`, `LemmaSeven.lean`, `LemmaEleven.lean`,
`Corollaries.lean` (`s₀ = e^{32}`, `c₃ = 4`; all constants explicit or existential and uniform).

1. **Calculus identities** (`Calculus.lean`). `mainMaj_true`/`mainMaj_false` (simp),
   `continuous_mainMaj`, `mainMaj_nonneg`, `mainMaj_antitone`, `mainMaj_le_MSieve`;
   `g_two_eq_integral : 2 ≤ s → IntegrableOn … ∧ g 2 s = ∫ t in Ioi s, max (3 - (t-1)) 0 / (t-1)`;
   `fSieve_eq_integral_mainMaj : 2 ≤ s → fSieve s = ∫ t in Ioi s, mainMaj false (t-1) / (t-1)`
   (integrability `integrableOn_mainMaj_false_shift`);
   `mainMaj_false_eq_integral (s) : mainMaj false s = max (3-s) 0 + ∫ t in Ioi (max s 3), fSieve (t-1)/(t-1)`.
   For `G`: `errLower lower` (`2` for `true`, `3` for `false`),
   `errMaj_eq_integral lower : errLower lower ≤ s → IntegrableOn (fun t => errMaj (!lower) (t-1) * t/(t-1)^2) (Ioi s) ∧
   errMaj lower s = ∫ t in Ioi s, errMaj (!lower) (t-1) * t/(t-1)^2`,
   `integral_errMaj_shift : errLower lower ≤ s → s ≤ b → ∫ t in s..b, … = errMaj lower s - errMaj lower b`,
   `hasDerivAt_errMaj : errLower lower < t → HasDerivAt (errMaj lower) (-(errMaj (!lower) (t-1) * t/(t-1)^2)) t`,
   `errMaj_false_of_le_three` (`𝔉 = 1` on `s ≤ 3`), `errMaj_pos`, `errMaj_antitone`, `errMaj_mem`,
   `errMaj_le_two`, `errMaj_eq_majG`, `majG_add_two`.
2. **Lemma 7** (`LemmaSeven.lean`). `MSieve_lt_four_mul_bigM : 2 ≤ s → MSieve s < 4 * bigM s` and
   `lemma7 r : 2 ≤ s → fr r s < MSieve s ∧ MSieve s ≤ 4 * bigM s` (false for `s < 2`, where
   `M(s) = 5 + F(3) - s`). On `[2,3]`, `M = (F(3)+3)(1 - log(s-1))` and `F(3) + 3 < 4`
   (`FSieve_three_add_lt_four`, from `fSieve_four_add`); for `s > 3` a first-crossing argument with
   `(s-1)M(s) = ∫_{s-1}^s M` (`sub_one_mul_MSieve`) and `∫_{s-1}^s 𝔐 ≤ (s-1)²𝔐(s)/s`
   (`integral_bigM_le`, from (3.12)). Consequences: `mainMaj_le_errMaj : 2 ≤ s →
   mainMaj lower s ≤ 12 * errMaj lower' s`, `MSieve_sub_one_lt : 3 ≤ s → MSieve (s-1) < 16 s² 𝔐(s)`,
   `mainMaj_sub_one_le : 1 ≤ s → mainMaj lower (s - 1) ≤ 48 * s^2 * errMaj lower' s` (any flags).
3. **Lemmas 11, 12** (`LemmaEleven.lean`). Hypotheses `exp 32 ≤ s`, `s ≤ b`,
   `b^2 * log b^4 ≤ log y^2 / 160` (i.e. `20 c₃ b² log⁴ b / L² ≤ 1/2`; it passes to smaller `b ≥ 1`,
   `sq_mul_log_pow_four_le_of_le`):
   `lemma11 r : ∫ t in s..b, (1 + t^2 * log t^5 / log y^2) ^ (5*(t-1)) * majG r (t-1) * t / (t-1)^2
   < delta s y * majG (r+1) s`;
   `lemma12 r : AntitoneOn (fun t => (1 + t^2 * log t^5 / L^2) ^ (5*(t-1)) * majG (r+1) t) (Icc s b)`;
   `antitoneOn_cor3Weight r : AntitoneOn (fun t => (1 + t^2 log t^5/L^2)^(5(t-1)) * majG r (t-1) * (t^2/(t-1)^2)) (Icc s b)`
   (the monotonicity of `b(x)` in Corollary 3, which [I71] attributes to Lemma 12; proved from the
   Corollary to Lemma 10 at `t - 1`). Core estimates: `hasDerivAt_growth`, `rate_bound`
   (`(log A_a)' ≤ w(15 log t + 25)` with `w = t² log⁴ t / L²`), `majG_succ_mul_log_lt`,
   `antitoneOn_growth_mul`. Size of `ξ`: `xi_sq_mul_log_pow_four_div_le : 1 < y → 1 ≤ log log 3y →
   1 ≤ ξ → ξ² log⁴ ξ / L² ≤ (log log 3y)^{-2/5}`, `tendsto_xi`, and
   `exists_xi_large : ∃ y₀, ∀ y ≥ y₀, 1 < y ∧ exp 32 ≤ xi y ∧ xi y^2 * log (xi y)^4 ≤ log y^2/160 ∧ 2 ≤ y^(1/xi y)`.
4. **Corollaries 1 and 3** (`Corollaries.lean`), `t_p = log y / log p`, `log (y/p) = log p (t_p - 1)`
   (`log_div_prime_eq`). `lemma13_param`: Lemma 13 after the substitution `u = y^{1/t}`
   (`integral_comp_log_div`): for `F ≥ 0` antitone on `[α, β]`, `0 < α`, `y^{1/β} ≥ 2`, and `S`
   between the primes in `(y^{1/β}, y^{1/α})` and in `[y^{1/β}, y^{1/α}]`,
   `|∑_{p∈S} F(t_p)/p - ∫ t in α..β, F t / t| ≤ C * F α * pntE (y^(1/β))`.
   `cor1 : ∃ C, 0 ≤ C ∧ ∀ M y α β, 1 < y → 2 ≤ α → α ≤ β → 2 ≤ y^(1/β) → AntitoneOn M (Icc (α-1) (β-1)) →
   (∀ t ∈ Icc (α-1) (β-1), 0 ≤ M t) → |∑ p ∈ (primesLT (y^(1/α))).filter (y^(1/β) ≤ ·),
   M (t_p - 1) / (p * log (y/p)) - (∫ t in α..β, M (t-1)/(t-1)) / log y| ≤ C * M (α-1) * pntE (y^(1/β)) / log y`
   (one-sided `cor1_le`).
   `cor3 : ∃ C, 0 ≤ C ∧ ∀ lower y s b, 1 < y → sMin lower ≤ s → exp 32 ≤ b → 2 ≤ y^(1/b) →
   b^2 * log b^4 ≤ log y^2/160 → ∑ p ∈ (rosserPrimes lower y (y^(1/s))).filter (y^(1/b) ≤ ·),
   delta (t_p - 1) (y/p) * errMaj (!lower) (t_p - 1) / (p * log (y/p)^2) ≤
   delta (max s (exp 32)) y * errMaj lower s / log y^2 * (1 + C * b^2 * pntE (y^(1/b)))`;
   `cor3_xi` is the case `b = ξ(y)`, `y ≥ y₀`. The sum is over the primes of the recursion
   (`rosserPrimes false` has `p³ < y`, so the upper-sieve case `s < 3` reduces to `s = 3`,
   `lt_rpow_one_div_max_three`); `cor3_primesLT` is the `primesLT` form for `errLower lower ≤ s`.
   Parts: `cor3_summand_le` (`δ(t-1, y/p) ≤ (1 + t² log⁵ t/L²)^{5(t-1)}`), `cor3_large`
   (`e^{32} ≤ s`: Lemmas 11, 12, 13), `cor3_small` (`s ≤ a ≤ e^{32}`: `δ ≤ δ(e^{32})`, Lemma 13
   for `G'(t-1) t²/(t-1)²` and `integral_errMaj_shift`), `errMaj_shift_sq_le : 2 ≤ s →
   errMaj lower' (s-1) * (s^2/(s-1)^2) ≤ 32 * s^2 * errMaj lower s`, `growth_le_delta`.
5. **Crude bound** (done, `LinearSieve/Crude.lean`; [I71] pp. 24, 27). A failing tuple of depth
   `l` has `z^{l+2} > y` and contributes `≤ 1/(p₁⋯p_l)`; the discrete integration
   `sum_SLT_pow_div_le : ∑_{p<z} SLT(p)^n / p ≤ SLT(z)^{n+1}/(n+1)` (from the general
   `sum_pow_sum_lt_mul_le`) replaces elementary symmetric sums. No hypotheses:
   `fail_le_sum_SLT_pow lower r y z :
     fail lower r y z ≤ ∑ l ∈ Icc 1 r with y < z ^ (l + 2), SLT z ^ l / l!`
   (shifted form `fail_le_sum_ite`). Tail: `sum_pow_div_factorial_le : 0 ≤ X → 0 < u →
   2 e X ≤ u → (∀ l ∈ s, u < l) → ∑ l ∈ s, X^l/l! ≤ 2 (e X / u)^u` (rpow), with
   `pow_div_factorial_le_pow : X^k/k! ≤ (e X/k)^k` and
   `exp_one_mul_div_rpow : (e X / u)^u = exp (-(u log u) + u log X + u)` (`X, u > 0`).
   Combined: `fail_le_tail : 1 < z → 0 < u → z^(u+2) ≤ y → SLT z ≤ X → 2 e X ≤ u →
   fail lower r y z ≤ 2 (e X / u)^u`, and `fail_rpow_le_tail` (`z = y^{1/s}`, `u = s - 2`,
   `1 < y`, `2 < s`); this is [I71]'s `Q_{m+1,y}(ξ-1) < Σ_{k>ξ-3} (Σ 1/p)^k/k! < (5 loglog y/ξ)^ξ`.
   `SLT_le_loglog : ∃ C, ∀ z ≥ 2, SLT z ≤ log (log z) + C`.
   Counts ([I71] p. 27): `lt_of_mem_rosserSet` (elements with `ω(d) ≥ 2`, or `≥ 1` for the
   upper sieve, are `< y`), `sum_inv_filter_card_primeFactors_eq_le :
   ∑_{d ∈ D, ω(d) = l} 1/d ≤ SLT(z)^l / l!`,
   `card_filter_le_mul_sum : 0 ≤ y → (if lower then 2 else 1) ≤ k →
   #{d ∈ D | k ≤ ω(d)} ≤ y ∑_{l ∈ Icc k π(z)} SLT(z)^l / l!`, `card_filter_le_tail`
   (`≤ 2 y (e X/u)^u` for `u < k`, `SLT z ≤ X`, `2 e X ≤ u`), and
   `card_filter_eq_le_pow_div : #{d ∈ D | ω(d) = l} ≤ π(z)^l / l!`.
6. **Depth stabilisation** (done, `LinearSieve/Depth.lean`). `LeProdPrimesLT r y z :=
   ∀ T ⊆ primesLT z, #T = r → y ≤ ∏_{p ∈ T} p` (Iwaniec's `p₁⋯p_r ≥ y`), with
   `LeProdPrimesLT.div` (`r+1` at `(y, z)` ⇒ `r` at `(y/p, p)`), `.succ`, `.mono`,
   `factorial_card_add_one_le_prod` (`r` distinct integers `≥ 2` have product `≥ (r+1)!`),
   `leProdPrimesLT_of_le_factorial : y ≤ (r+1)! → LeProdPrimesLT r y z`.
   `fail_add_eq : 2 ≤ r → LeProdPrimesLT r y z → fail lower (r + j) y z = fail lower r y z`
   (base case `r = 2`: the pass condition two levels up; `r = 1` is false for the lower sieve),
   `fail_add_eq_of_le_factorial` (`y ≤ (r+1)!`);
   `card_filter_rosserSet_add_eq : 1 ≤ r → LeProdPrimesLT (r + 1) y z →
   #{d ∈ D | ω(d) ≤ r + j} = #{d ∈ D | ω(d) ≤ r}` (via `card_primeFactors_le_of_mem_rosserSet`).
   Numerics: `exists_le_factorial : ∃ y₀, ∀ y ≥ y₀, ∀ r : ℕ, 2 log y / log log y < r + 2 →
   2 ≤ r ∧ y ≤ (r+1)!` (`y₀ = exp (exp 49)`, via `n (log n - 1) ≤ log n!`), hence
   `exists_fail_add_eq : ∃ y₀, ∀ y ≥ y₀, ∀ lower r z, 2 log y / log log y < r + 2 →
   ∀ j, fail lower (r + j) y z = fail lower r y z` ([I71]: `m + 1 > 2 log y/loglog y ⇒
   Q_{m+1} = Q_{m-1}`, with `r = m - 1`) and `exists_card_filter_rosserSet_add_eq` (same, for
   `#{d ∈ D | ω(d) ≤ r - 1 + j} = #{d ∈ D | ω(d) ≤ r - 1}`, which gives [I71]'s
   `A_{m+1} = A_{m-1}`).
7. **Theorem 4** (main terms; done, `LinearSieve/TheoremFour.lean`, helpers in
   `TheoremFourAux.lean`, `TheoremFourAsymp.lean`, namespace `IwaniecJacobsthal.TheoremFour`).

       theorem theorem4 {cR CR : ℝ} (hcR : 0 < cR)
           (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
           ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
             s ≤ xi y → fail lower r y (y ^ (1 / s)) ≤
               cR * (mainMaj lower s / log y +
                 c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2)

   (apply it to the `cR`, `CR` obtained from `R_asymp`). Proof as in [I71, pp. 23–25], by
   induction on `r` for both sieves at once (`TheoremFour.Bound cR c₇ r`), with
   `y₀` (all "large `y`" facts) fixed first and then `c₇ = max (32/cR) (6 e^{SLT y₀} log² y₀ /
   (cR 𝔐(Ξ)))`, `Ξ = log y₀ / (log log 3)^{11/5}`:
   * `y ≤ y₀` (`small_y`, (4.8)): `fail ≤ exp (SLT y₀)` (`fail_le_exp_SLT`), `s ≤ ξ(y) ≤ Ξ`, and
     the error term alone is large enough;
   * `2L / log L < r + 2`: `fail (r+1) = fail r` (`exists_fail_add_eq`);
   * otherwise (`main_step`) split at `w = y^{1/ξ}` (not `y^{1/(ξ-1)}`: then
     `t_p - 1 ≤ ξ(y/p)` exactly, `inner_le_xi`) by `fail_succ_le_split` into
     `fail (r+1) y w`, the large primes and the source term `src` (`= R(y^{1/3}) - R(z)`,
     `sum_R_div_eq`, bounded by `R_asymp` in `src_le`). Large primes: IH at
     `(y/p, t_p - 1)` (`ih_term`, `rpow_inner_eq`, `sMin_le_inner`), `cor1_part`
     (`cor1_le` + `fSieve_eq_integral_mainMaj` / `mainMaj_false_eq_integral`, error via
     `mainMaj_sub_one_le`), `cor3_xi`, `delta_max_le`. Small primes: `crude_le`
     (`fail_rpow_le_tail` with `X = log log w + C`, against `majG_ge_exp` at `ξ/2` resp.
     `δ(ξ/2, y) G(ξ)`; [I71, (4.4), (4.5), (4.9), (4.10)]). Bookkeeping `combine`, `ratio_le`:
     `r/(r+1) ≤ (r+1)/(r+2) (1 - ε)` with `ε = (log L)²/(4L²)` from `(r+1) log L ≤ 2L`
     ([I71, (4.6)]); the losses `δ(s₀,y)(1 + C₃ ξ² pntE w) ≤ 1 + ε/2`
     (`eventually_delta_mul_le`), `K ξ² L³ pntE w ≤ 1` (`eventually_mul_pntE_le`) and the crude
     part `≤ δ G / L⁴` fit into `c₇ cR (r+1)/(r+2) · ε/2 · δ G / L²` once `cR c₇ ≥ 32`.
   The asymptotics are proved in the variable `ℓ = log log 3y` (`L = e^ℓ - log 3`,
   `log w = ℓ^{11/5}`, `pntE w = exp(-κ ℓ^{11/10})`; `crude_alg`, `eventually_crude_hyp`).
   Note: `(3 + (-1)^r)/2 ≤ s` in [I71] is our `sMin lower ≤ s`; no boundary adjustment was needed.
8. **Theorem 5** (support counts; done, `LinearSieve/TheoremFive{Aux,Count,}.lean`, helpers in
   `namespace IwaniecJacobsthal.TheoremFive`):

       theorem5 : ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y →
         sMin lower ≤ s → s ≤ xi y →
         (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
           c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2

       theorem5_card_rosserSet_le : ∃ K y₀ : ℝ, ∀ y ≥ y₀, ∀ s ∈ Set.Icc (2 : ℝ) 3,
         (#(rosserSet true y (y ^ (1 / s))) : ℝ) ≤ K * y / log y ^ 2

   Indexing: [I71]'s `A_{r,y}` counts `r + 1` levels, whence his `r/(r+1)` and `G_{r+1}`; with
   Lemma 17 in the form `card_filter_rosserSet_succ` (count at flag `lower` = `1 + Σ_p` count at
   `!lower`), the majorant at flag `lower` is `errMaj lower` and the factor is `(r+1)/(r+2)`
   (positive at `r = 0`, where the count is `1`). The consequence takes `r = #(primesLT z)`,
   `δ(s, y) ≤ (1 + 9 log⁵ 3)^{15}` (`delta_le_of_le_three`) and `𝔣 ≤ 2`.
   Proof (induction on `r`, both flags; `exists_bound`, with `Bound c₇ r` the statement at depth
   `r`). Constants in order: `c_G` (Lemma 9, `majG_ge_exp`), `C₅` (`SLT_le_loglog`), `C`
   (`cor3_xi`); then `c₈` = max of the thresholds of `exists_card_small`, `cor3_xi`,
   `exists_slack C`, `exists_card_filter_rosserSet_add_eq`, `exists_xi_large`, and `3`; then
   `c₇ = max 1 (2 log² c₈ / min (𝔣(Ξ), 𝔉(Ξ)))` with `Ξ = log c₈ / (log log 3)^{11/5} ≥ ξ(y)` for
   `y < c₈` (`xi_le_of_lt`). Cases:
   * `y < c₈` (`small_le`): all elements are `< y` (`lt_of_mem_rosserSet_rpow`), so the count is
     `≤ y` (`card_rosserSet_le`);
   * `r = 0`, `y ≥ c₈`: the count is `1 ≤ δ G y / (8 L⁴)` (from `exists_card_small`);
   * `y ≥ c₈`, `r + 3 > 2L/log L`: `exists_card_filter_rosserSet_add_eq` (count at `r + 1` =
     count at `r`);
   * main case (`step_main`): Lemma 17 split at `w = y^{1/(ξ-1)}` (`card_filter_succ_le`: the
     primes `p < w` and the `1` give `≤ #(rosserSet lower y w)`); for `p ≥ w`, `t_p ≤ ξ - 1`,
     the IH at `(y/p, t_p - 1)` (`inner_le`: `t_p - 1 ≤ ξ(y/p)` by `sub_one_le_xi_div`,
     `(y/p)^{1/(t_p-1)} = p`, `sMin (!lower) ≤ t_p - 1` by `rosserPrimes_facts`, which also
     covers the upper sieve with `s < 3` since `p³ < y`), then `cor3_xi`. With
     `Q = δ(s,y) G(s) y/L²`, `ε = (log L)²/(8L²)`, `X = δ(s₀,y)(1 + C ξ² pntE(y^{1/ξ})) - 1`:
     `δ(max s s₀) ≤ δ(s) δ(s₀)` (`delta_max_le`), `X ≤ ε` (`exists_slack`: `δ(s₀,y) ≤ e^{K/L²}`,
     `C ξ² pntE(y^{1/ξ}) ≤ 1/L²` since `log y^{1/ξ} = λ^{11/5}`), the crude part `≤ Q ε`, and
     `(r+2)/(r+3) - (r+1)/(r+2) ≥ 2ε` from `r + 3 ≤ 2L/log L` (`gap_le`); `close_step` closes.
   The crude part (`exists_card_small`, [I71, p. 27] with (4.9), (4.10)): with `λ = lam y =
   log log 3y`, `u = ξ(1 - 2/λ)`, `K = ⌊u⌋`: elements with `ω ≤ K` number `≤ (K+1)(2w)^K ≤
   e^{L + 2ξ - L/λ}` (`card_filter_le_le`, `π(w) ≤ w + 1`), the others `≤ 2y(2eλ/u)^u ≤
   2e^{L - ξ log ξ + ξ log λ + 5ξ}` (`card_filter_le_tail`, `u log u ≥ ξ log ξ - 3ξ`);
   `crude_exponent_le` gives `8L⁴(1 + #) ≤ y e^{-ξ log ξ + (3/2) ξ log λ}`, and
   `exp_le_delta_errMaj` gives `e^{-ξ log ξ + (3/2) ξ log λ} ≤ δ(s,y) G(s)` for `sMin ≤ s ≤ ξ`
   (`s ≤ ξ/2`: Lemma 9 at `max s 3`; `s > ξ/2`: `δ ≥ (s² log⁵ s/L²)^{5s} ≥ e^{s(3 log λ - 5 log
   128)}`, using `ξ²λ⁵/L² = λ^{3/5}`). All "large `y`" facts come from `eventually_scalar`
   (`λ, log λ, λ^{1/5} ≥ c`, `λ - 1 ≤ log L ≤ λ`, `24λ ≤ ξ`, `16λ² ≤ L`, `λ/2 ≤ log(ξ/2)`,
   `4 log λ + c ≤ log ξ ≤ λ`), proved from `log x = o(x)`.
9. **`LinearSieveEstimate`.** With `y = C₀ z²`, `s = 2 + log C₀ / log z ∈ [2, 2.5]`: take `r` large
   (`fail_eq_of_card_lt`), then use Theorem 4, `R_asymp` (`R z = cR s/L · (1 + O(pntE))`) and
   `one_sub_fSieve_div_ge`. This gives
   `R z - rosserMain true y z ≤ R z (f(s)/s + O(1/L)) ≤ R z (1 - 3 log(s-1)/s + O(1/L))`,
   and `3 log(s-1)/s ≥ log C₀ / log z` once `z` is large; choose `C₀` with `log C₀` larger than
   twice the `O`-constant. Theorem 5 gives the support count `≪ y/L²`.
