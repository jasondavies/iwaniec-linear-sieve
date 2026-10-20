module

public import IwaniecLinearSieve.General.Defs
public import IwaniecLinearSieve.General.LemmaOne
public import IwaniecLinearSieve.General.RosserK
public import IwaniecLinearSieve.General.Totient
public import IwaniecLinearSieve.General.LemmaSixteen

@[expose] public section

/-!
# [I71, §2] for general `k` and sequences

`A_k(M; z)`, `|M_d|` and `R_k` for a finite sequence (multiset) `M` of integers; Lemma 1 with
arbitrary truncation functions (`lemma1_upper`, `lemma1_lower`) and its Corollary, Lemma 2,
(2.12), (2.13); `k/φ(k) ≪ log log 3k`; Lemma 16 (`lemma16`).
-/
