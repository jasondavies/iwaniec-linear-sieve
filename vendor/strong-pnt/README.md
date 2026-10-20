# strong-pnt

The prime number theorem with de la Vallée Poussin error term,

    theorem StrongPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1/2))

with the 15 files of its import closure, and Mertens' theorems with the constant `e^{-γ}`
(`PrimeNumberTheoremAnd/IEANTN/Mertens.lean` upstream, which needs only `EulerMaclaurin` and `Architect`
besides Mathlib), for instance

    theorem Mertens.E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop]
      (fun x ↦ exp (-eulerMascheroniConstant) / log x)

from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Apache 2.0,
see `LICENSE`), ported from Lean 4.34.0 to Lean 4.35.0 / Mathlib v4.35.0 and to the Lean module
system.

All files live under the module prefix `IwaniecLinearSieveVendor` (upstream module `M` is
`IwaniecLinearSieveVendor.M`), so this copy can sit in the same Lake workspace as
PrimeNumberTheoremAnd or LeanArchitect without module-name collisions. The declarations keep their
upstream names (`StrongPNT`, `Mertens.E₃.bound''`, …), so a single file cannot import both this
copy and PrimeNumberTheoremAnd.

* `IwaniecLinearSieveVendor/Architect.lean` is a local no-op replacement for LeanArchitect: it
  accepts the `@[blueprint ...]` attribute and `blueprint_comment` command and ignores them.
* `IwaniecLinearSieveVendor/PrimeNumberTheoremAnd/Mathlib/Tactic/LinearCombinationPrime.lean` is
  Mathlib v4.34.0's `Mathlib/Tactic/LinearCombinationPrime.lean` (Apache 2.0), removed from Mathlib
  in v4.35.0.
* `UPSTREAM.json` records the upstream revisions and path of every file, the SHA-256 of every
  upstream and local file, the mechanical rewrite to the Lean module system, and the local
  patches to seven files.
