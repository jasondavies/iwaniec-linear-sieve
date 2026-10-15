import IwaniecJacobsthal.SieveFunctions.Defs
import IwaniecJacobsthal.SieveFunctions.Bounds
import IwaniecJacobsthal.SieveFunctions.Series
import IwaniecJacobsthal.SieveFunctions.LemmaFive

/-!
# The sieve functions of [I71, §3]

* `IwaniecJacobsthal.g`: Iwaniec's `g_n` (3.1)–(3.3), with `g_two_eq`, `g_two_of_four_le`,
  `g_odd_eq_integral`, `g_odd_of_le_three`, `g_even_eq_integral`, `continuous_g`, `g_nonneg`,
  `g_pos`, `g_antitone`, `g_eq_zero_of_le`.
* Lemma 3: `psi_le_psi_two`. Lemma 4: `g_odd_le'` (3.4), `g_even_le` (3.5), with constants
  `gLead` (`a`) and `gRatio` (`A`), `gRatio_lt : gRatio < 0.72`.
* Corollary: `fSieve` (`f`), `FSieve` (`F`), `fr`; `continuous_fSieve`, `fSieve_pos`,
  `fSieve_le`, `fSieve_eq_integral` (3.6), `FSieve_eq_integral`, `FSieve_of_le_three` (3.7), ...
* Lemma 5: `fSieve_eq_on_Icc'` (3.9), `fSieve_two` (3.10), `fSieve_eq_on_Icc`,
  `one_sub_fSieve_div_ge`.
-/
