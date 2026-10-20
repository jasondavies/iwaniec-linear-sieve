module

import all IwaniecLinearSieve.Basic
import all IwaniecLinearSieve.Definitions
import all IwaniecLinearSieve.EulerGamma
import all IwaniecLinearSieve.EulerGamma.Buchstab
import all IwaniecLinearSieve.EulerGamma.LemmaFive
import all IwaniecLinearSieve.EulerGamma.Mertens
import all IwaniecLinearSieve.EulerGamma.TheoremFour
import all IwaniecLinearSieve.General
import all IwaniecLinearSieve.General.Defs
import all IwaniecLinearSieve.General.LemmaOne
import all IwaniecLinearSieve.General.LemmaSixteen
import all IwaniecLinearSieve.General.RosserK
import all IwaniecLinearSieve.General.Totient
import all IwaniecLinearSieve.Jacobsthal
import all IwaniecLinearSieve.Jacobsthal.LemmaOne
import all IwaniecLinearSieve.Jacobsthal.LemmaTwo
import all IwaniecLinearSieve.Jacobsthal.Reduction
import all IwaniecLinearSieve.Jacobsthal.ShiftedSieve
import all IwaniecLinearSieve.Jacobsthal.Theorem
import all IwaniecLinearSieve.LinearSieve
import all IwaniecLinearSieve.LinearSieve.Calculus
import all IwaniecLinearSieve.LinearSieve.Corollaries
import all IwaniecLinearSieve.LinearSieve.Crude
import all IwaniecLinearSieve.LinearSieve.Defs
import all IwaniecLinearSieve.LinearSieve.Depth
import all IwaniecLinearSieve.LinearSieve.Estimate
import all IwaniecLinearSieve.LinearSieve.LemmaEleven
import all IwaniecLinearSieve.LinearSieve.LemmaSeven
import all IwaniecLinearSieve.LinearSieve.TheoremFive
import all IwaniecLinearSieve.LinearSieve.TheoremFiveAux
import all IwaniecLinearSieve.LinearSieve.TheoremFiveCount
import all IwaniecLinearSieve.LinearSieve.TheoremFour
import all IwaniecLinearSieve.LinearSieve.TheoremFourAsymp
import all IwaniecLinearSieve.LinearSieve.TheoremFourAux
import all IwaniecLinearSieve.Main
import all IwaniecLinearSieve.Main.Basic
import all IwaniecLinearSieve.Main.Corollary
import all IwaniecLinearSieve.Main.Fundamental
import all IwaniecLinearSieve.Main.TheoremOne
import all IwaniecLinearSieve.Main.TheoremOneFull
import all IwaniecLinearSieve.Main.TheoremThree
import all IwaniecLinearSieve.Main.TheoremTwo
import all IwaniecLinearSieve.PrimeSums
import all IwaniecLinearSieve.PrimeSums.Error
import all IwaniecLinearSieve.PrimeSums.Lemma13
import all IwaniecLinearSieve.PrimeSums.Mertens
import all IwaniecLinearSieve.PrimeSums.NthPrime
import all IwaniecLinearSieve.PrimeSums.Product
import all IwaniecLinearSieve.PrimeSums.SummationByParts
import all IwaniecLinearSieve.Rosser
import all IwaniecLinearSieve.SieveFunctions
import all IwaniecLinearSieve.SieveFunctions.Bounds
import all IwaniecLinearSieve.SieveFunctions.Defs
import all IwaniecLinearSieve.SieveFunctions.LemmaFive
import all IwaniecLinearSieve.SieveFunctions.Series
import all IwaniecLinearSieve.SieveMajorants
import all IwaniecLinearSieve.SieveMajorants.Asymptotic
import all IwaniecLinearSieve.SieveMajorants.Defs
import all IwaniecLinearSieve.SieveMajorants.Delay
import all IwaniecLinearSieve.SieveMajorants.Dickman
import all IwaniecLinearSieve.SieveMajorants.Lemmas
import all IwaniecLinearSieve.SieveMajorants.Majorants
import all IwaniecLinearSieve.SieveMajorants.Properties
import all IwaniecLinearSieveVendor.Architect
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Auxiliary
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.EulerMaclaurin
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Fourier
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.IEANTN.Mertens
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Mathlib.Tactic.LinearCombinationPrime
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.MediumPNT
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.MellinCalculus
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Rectangle
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.SmoothExistence
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Sobolev
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.StrongPNT
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.Tactic.AdditiveCombination
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.ZetaBounds
import all IwaniecLinearSieveVendor.PrimeNumberTheoremAnd.ZetaConj
meta import Lean

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in this library's modules and in the vendored prime number theorem
sources, covering declarations in other namespaces, private declarations, and generated
declarations. Private declarations are visible only through `import all`, so every source
module is imported that way. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- A source added outside the umbrella import graph must not escape the audit.
  let scriptDir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let repoRoot ← IO.FS.realPath (scriptDir / "..")
  let sourceRoots : Array (System.FilePath × Name) := #[
    (repoRoot / "IwaniecLinearSieve", `IwaniecLinearSieve),
    (repoRoot / "vendor" / "strong-pnt" / "IwaniecLinearSieveVendor", `IwaniecLinearSieveVendor)]
  for (sourceRoot, root) in sourceRoots do
    for path in (← sourceRoot.walkDir) do
      if path.extension == some "lean" then
        let parts := (path.withExtension "").components.drop sourceRoot.components.length
        let moduleName := parts.foldl Name.str root
        unless env.header.imports.any (fun i => i.module == moduleName && i.importAll) do
          throwError "Add `import all {moduleName}` to scripts/CheckAxioms.lean"
  -- Module tables avoid scanning every declaration imported from Mathlib.
  let audited : Array Name := #[`IwaniecLinearSieve, `IwaniecLinearSieveVendor]
  -- A renamed library must not silently drop out of the audit.
  for pre in audited do
    unless env.header.moduleNames.any (pre.isPrefixOf ·) do
      throwError "No imported module under {pre}"
  let mut names : Array Name := #[]
  for moduleName in env.header.moduleNames, moduleData in env.header.moduleData do
    if audited.any (·.isPrefixOf moduleName) then
      names := names ++ moduleData.constNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Under the module system, imported Mathlib theorems carry no proofs in this environment, so
  -- a hand-written traversal would see them as axioms. `collectAxioms` instead uses the axiom
  -- sets that Lean records for every declaration when it compiles each module, and traverses
  -- theorem and opaque bodies.
  for name in names do
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  let countFrom (pre : Name) := (names.filter fun name =>
    match env.getModuleIdxFor? name with
    | some idx => pre.isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false).size
  logInfo m!"Audited {names.size} declarations ({countFrom `IwaniecLinearSieve} Iwaniec linear sieve, {countFrom `IwaniecLinearSieveVendor} vendored prime number theorem); only propext, Classical.choice and Quot.sound found."
