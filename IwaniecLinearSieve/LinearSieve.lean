module

public import IwaniecLinearSieve.LinearSieve.Defs
public import IwaniecLinearSieve.LinearSieve.Depth
public import IwaniecLinearSieve.LinearSieve.Crude
public import IwaniecLinearSieve.LinearSieve.Calculus
public import IwaniecLinearSieve.LinearSieve.LemmaSeven
public import IwaniecLinearSieve.LinearSieve.LemmaEleven
public import IwaniecLinearSieve.LinearSieve.Corollaries
public import IwaniecLinearSieve.LinearSieve.TheoremFourAux
public import IwaniecLinearSieve.LinearSieve.TheoremFourAsymp
public import IwaniecLinearSieve.LinearSieve.TheoremFour
public import IwaniecLinearSieve.LinearSieve.TheoremFiveAux
public import IwaniecLinearSieve.LinearSieve.TheoremFiveCount
public import IwaniecLinearSieve.LinearSieve.TheoremFive
public import IwaniecLinearSieve.LinearSieve.Estimate

@[expose] public section

/-!
# The linear sieve at the sifting limit ([I71, §4])

Lemmas 7, 11, 12 and Corollaries 1–3, the crude bounds, Theorem 4 (`theorem4`: the main term
with error `O(1/log y)`), Theorem 5 (`theorem5`: support of size `O(y / log² y)`), and the
estimate used for [I78] (`linearSieveEstimate`).
-/
