import IwaniecLinearSieve.LinearSieve.Defs
import IwaniecLinearSieve.LinearSieve.Depth
import IwaniecLinearSieve.LinearSieve.Crude
import IwaniecLinearSieve.LinearSieve.Calculus
import IwaniecLinearSieve.LinearSieve.LemmaSeven
import IwaniecLinearSieve.LinearSieve.LemmaEleven
import IwaniecLinearSieve.LinearSieve.Corollaries
import IwaniecLinearSieve.LinearSieve.TheoremFourAux
import IwaniecLinearSieve.LinearSieve.TheoremFourAsymp
import IwaniecLinearSieve.LinearSieve.TheoremFour
import IwaniecLinearSieve.LinearSieve.TheoremFiveAux
import IwaniecLinearSieve.LinearSieve.TheoremFiveCount
import IwaniecLinearSieve.LinearSieve.TheoremFive
import IwaniecLinearSieve.LinearSieve.Estimate

/-!
# The linear sieve at the sifting limit ([I71, §4])

Lemmas 7, 11, 12 and Corollaries 1–3, the crude bounds, Theorem 4 (`theorem4`: the main term
with error `O(1/log y)`), Theorem 5 (`theorem5`: support of size `O(y / log² y)`), and the
estimate used for [I78] (`linearSieveEstimate`).
-/
