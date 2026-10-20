module

public import IwaniecLinearSieve.PrimeSums.Error
public import IwaniecLinearSieve.PrimeSums.Mertens
public import IwaniecLinearSieve.PrimeSums.Product
public import IwaniecLinearSieve.PrimeSums.SummationByParts
public import IwaniecLinearSieve.PrimeSums.Lemma13
public import IwaniecLinearSieve.PrimeSums.NthPrime

@[expose] public section

/-!
# Prime sums with de la Vallée Poussin error terms, from `StrongPNT`

* `IwaniecLinearSieve.PrimeSums.Error`: the error term `pntE x = exp (-pntκ √(log x))` and
  `theta_asymp : |θ x - x| ≤ C x pntE x` for `x ≥ 2`.
* `IwaniecLinearSieve.PrimeSums.Mertens`: `S x = ∑_{p ≤ x} 1/p` and `S_asymp`.
* `IwaniecLinearSieve.PrimeSums.Product`: `R_asymp`, `R_lower`, `R_upper`.
* `IwaniecLinearSieve.PrimeSums.SummationByParts`: an abstract summation by parts bound.
* `IwaniecLinearSieve.PrimeSums.Lemma13`: [I71, Lemma 13] (`lemma13_mono`, `lemma13_anti`) and
  [I71, Lemma 14] (`lemma14`).
* `IwaniecLinearSieve.PrimeSums.NthPrime`: `nth_prime_le`.
-/
