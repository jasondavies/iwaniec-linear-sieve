import IwaniecJacobsthal.SieveMajorants.Delay
import IwaniecJacobsthal.SieveMajorants.Defs
import IwaniecJacobsthal.SieveMajorants.Properties
import IwaniecJacobsthal.SieveMajorants.Majorants
import IwaniecJacobsthal.SieveMajorants.Lemmas

/-!
# [I71, §3]: the functions `𝔐`, `𝔚`, `𝔣`, `𝔉`, `G_r`

* `Delay`: generic construction of solutions of `y'(s) = k(s) y(s-1)` and a first-crossing
  principle.
* `Defs`: `bigM` (`𝔐`), `bigW` (`𝔚`); (3.11) `bigW_eq_neg_mul_integral`, (3.12)
  `bigM_integral_identity`.
* `Properties`: `bigM_pos`, `bigM_antitone`, `bigM_le_exp`, Lemma 6 `abs_bigW_le`.
* `Majorants`: `majf` (`𝔣`), `majF` (`𝔉`), `majG` (`G_r`); (3.13) `majF_eq_integral`, (3.14)
  `majf_eq_integral`, Corollary to Lemma 6 `majG_mem`, `majG_antitone`, `hasDerivAt_majG_succ`.
* `Lemmas`: Lemma 8 `bigM_sub_one_lt`, Lemma 10 `bigM_mul_log_div_lt` and its Corollary
  `majG_succ_mul_log_div_lt`, Lemma 9 (lower bound) `majG_ge_exp`.
-/
