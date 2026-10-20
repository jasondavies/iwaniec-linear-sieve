module

public import IwaniecLinearSieve.Main.Basic
public import IwaniecLinearSieve.Main.TheoremOne
public import IwaniecLinearSieve.Main.Fundamental
public import IwaniecLinearSieve.Main.Corollary
public import IwaniecLinearSieve.Main.TheoremTwo
public import IwaniecLinearSieve.Main.TheoremThree
public import IwaniecLinearSieve.Main.TheoremOneFull

@[expose] public section

/-!
# The main results of [I71] (§1, §5)

Theorem 1 (`theorem1`, and `theorem1_full` with the formulas for `f`, `F`, `𝔐`), its Corollary
(`corollary_upper`, `corollary_lower`), Theorem 2 (`theorem2`: `C₀(r) ≪ r² log² r`) and
Theorem 3 (`theorem3_fst`, `theorem3_snd`), with a fundamental lemma for small `z`
(`fundamental_lemma`).
-/
