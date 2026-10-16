import IwaniecLinearSieve.PrimeSums.Error
import IwaniecLinearSieve.PrimeSums.Mertens
import IwaniecLinearSieve.PrimeSums.Product
import IwaniecLinearSieve.PrimeSums.SummationByParts
import IwaniecLinearSieve.PrimeSums.Lemma13
import IwaniecLinearSieve.PrimeSums.NthPrime

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
