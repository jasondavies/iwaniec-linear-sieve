import IwaniecJacobsthal.PrimeSums.Error
import IwaniecJacobsthal.PrimeSums.Mertens
import IwaniecJacobsthal.PrimeSums.Product
import IwaniecJacobsthal.PrimeSums.SummationByParts
import IwaniecJacobsthal.PrimeSums.Lemma13
import IwaniecJacobsthal.PrimeSums.NthPrime

/-!
# Prime sums with de la Vallée Poussin error terms, from `StrongPNT`

* `IwaniecJacobsthal.PrimeSums.Error`: the error term `pntE x = exp (-pntκ √(log x))` and
  `theta_asymp : |θ x - x| ≤ C x pntE x` for `x ≥ 2`.
* `IwaniecJacobsthal.PrimeSums.Mertens`: `S x = ∑_{p ≤ x} 1/p` and `S_asymp`.
* `IwaniecJacobsthal.PrimeSums.Product`: `R_asymp`, `R_lower`, `R_upper`.
* `IwaniecJacobsthal.PrimeSums.SummationByParts`: an abstract summation by parts bound.
* `IwaniecJacobsthal.PrimeSums.Lemma13`: [I71, Lemma 13] (`lemma13_mono`, `lemma13_anti`) and
  [I71, Lemma 14] (`lemma14`).
* `IwaniecJacobsthal.PrimeSums.NthPrime`: `nth_prime_le`.
-/
