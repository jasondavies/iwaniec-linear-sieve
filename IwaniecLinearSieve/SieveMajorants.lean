module

public import IwaniecLinearSieve.SieveMajorants.Delay
public import IwaniecLinearSieve.SieveMajorants.Defs
public import IwaniecLinearSieve.SieveMajorants.Properties
public import IwaniecLinearSieve.SieveMajorants.Majorants
public import IwaniecLinearSieve.SieveMajorants.Lemmas
public import IwaniecLinearSieve.SieveMajorants.Asymptotic
public import IwaniecLinearSieve.SieveMajorants.Dickman

@[expose] public section

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
* `Asymptotic`: Theorem 1, the asymptotics of `𝔐` (`bigM_asymp`), by comparison with explicit
  sub- and supersolutions of (3.12); Lemma 9 in full (`majG_mul_exp_le`, `lemma9`).
* `Dickman`: the Dickman function `dickman` (`ϱ`), `ϱ = O(𝔐)`, `𝔐(s+2) = O(ϱ(s))`, and its
  asymptotics `dickman_asymp`.
-/
