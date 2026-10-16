import IwaniecLinearSieve.EulerGamma.Mertens
import IwaniecLinearSieve.EulerGamma.Buchstab
import IwaniecLinearSieve.EulerGamma.LemmaFive
import IwaniecLinearSieve.EulerGamma.TheoremFour

/-!
# Euler's constant in [I71]

* `IwaniecLinearSieve.EulerGamma.Mertens`: Mertens' third theorem with the constant `e^{-γ}`
  (`tendsto_R_mul_log`, `R_asymp_exp`, `eq_exp_neg_eulerMascheroniConstant_of_R`), from the
  vendored `PrimeNumberTheoremAnd.IEANTN.Mertens`.
* `IwaniecLinearSieve.EulerGamma.Buchstab`: Buchstab's function `buchstab` (`ω`), its uniqueness
  (`eqOn_buchstab`), its Laplace transform (`one_add_buchstabLaplace`) and de Bruijn's limit in
  Laplace form (`eq_exp_neg_of_integrableOn_buchstab_sub`).
* `IwaniecLinearSieve.EulerGamma.LemmaFive`: [I71, Lemma 5] in full: `wSieve_eqOn_buchstab`
  (`w = ω`), `FSieve_three` (`F(3) = 2e^γ - 3`), `tendsto_buchstab` (`ω(u) → e^{-γ}`),
  `fSieve_eq_of_mem_Icc`, `FSieve_eq_of_mem_Icc`, `MSieve_eq_of_mem_Icc` (Corollary).
* `IwaniecLinearSieve.EulerGamma.TheoremFour`: [I71, Theorem 4] in Iwaniec's normalisation
  (`theorem4_exp`).
-/
