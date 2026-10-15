# strong-pnt

The prime number theorem with de la Vallée Poussin error term,

    theorem StrongPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1/2))

with the 15 files of its import closure from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Apache 2.0,
see `LICENSE`), ported from Lean 4.34.0 to Lean 4.35.0 / Mathlib v4.35.0.

* `Architect.lean` is a local no-op replacement for LeanArchitect: it accepts the
  `@[blueprint ...]` attribute and `blueprint_comment` command and ignores them.
* `PrimeNumberTheoremAnd/Mathlib/Tactic/LinearCombinationPrime.lean` is Mathlib v4.34.0's
  `Mathlib/Tactic/LinearCombinationPrime.lean` (Apache 2.0), removed from Mathlib in v4.35.0.
* `UPSTREAM.json` records the upstream revisions, the SHA-256 of every upstream and local file,
  and the four local patches.
