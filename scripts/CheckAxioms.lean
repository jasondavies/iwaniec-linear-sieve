import IwaniecLinearSieve

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in this library's modules and in the vendored prime number theorem
sources, covering declarations in other namespaces, private declarations, and generated
declarations. -/

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
        unless env.header.moduleNames.contains moduleName do
          throwError "Source module is not imported by the audit: {moduleName}"
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
  -- Share one visited set across roots; inspect theorem and opaque bodies too.
  let mut pending := names.map fun name => (name, name)
  let mut visited : NameSet := {}
  while let some (origin, name) := pending.back? do
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      let some info := env.checked.get.find? name
        | throwError "Missing declaration {name} while auditing {origin}"
      if info.isAxiom && !allowed.contains name then
        throwError "Unexpected axiom {name} in {origin}"
      let mut dependencies := info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        dependencies := dependencies ++ value.getUsedConstants
      if let .inductInfo value := info then
        dependencies := dependencies ++ value.ctors.toArray
      for dependency in dependencies do
        pending := pending.push (origin, dependency)
  let countFrom (pre : Name) := (names.filter fun name =>
    match env.getModuleIdxFor? name with
    | some idx => pre.isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false).size
  logInfo m!"Audited {names.size} declarations ({countFrom `IwaniecLinearSieve} Iwaniec linear sieve, {countFrom `IwaniecLinearSieveVendor} vendored prime number theorem); only propext, Classical.choice and Quot.sound found."
