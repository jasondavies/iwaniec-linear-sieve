# strong-pnt

The prime number theorem with de la Vallée Poussin error term,

    theorem StrongPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1/2))

with the 14 files of its import closure, and Mertens' theorems with the constant `e^{-γ}`
(`PrimeNumberTheoremAnd/IEANTN/Mertens.lean` upstream, which needs only `EulerMaclaurin` and `Architect`
besides Mathlib), for instance

    theorem Mertens.E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop]
      (fun x ↦ exp (-eulerMascheroniConstant) / log x)

from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Apache 2.0,
see `LICENSE`), at revision `127b50e33f6033e2147921167a117af96d9ba4ea`, which uses
Lean 4.35.0 / Mathlib v4.35.0. The vendored sources are adapted to the Lean module system.
Most upstream files are still non-modules, so our module-based library cannot import them
directly through a pinned dependency.

All files live under the module prefix `IwaniecLinearSieveVendor` (upstream module `M` is
`IwaniecLinearSieveVendor.M`), so this copy can sit in the same Lake workspace as
PrimeNumberTheoremAnd or LeanArchitect without module-name collisions. The declarations keep their
upstream names (`StrongPNT`, `Mertens.E₃.bound''`, …), so a single file cannot import both this
copy and PrimeNumberTheoremAnd.

* `IwaniecLinearSieveVendor/Architect.lean` is a local no-op replacement for LeanArchitect: it
  accepts the `@[blueprint ...]` attribute and `blueprint_comment` command and ignores them.
* `UPSTREAM.json` records upstream revisions, paths and hashes for copied files, local
  SHA-256 hashes for every Lean source (including the local `Architect.lean` stand-in),
  the mechanical rewrite to the Lean module system, and the local patches to three files.
  The snapshot contains 15 upstream Lean files and the local `Architect.lean` stand-in.
