import ProjectEpisteme
import Lean.Util.CollectAxioms

/-!
Transitive axiom audit for the assembled library. Run it after building the root module:
`lake env lean -DwarningAsError=true checks/AxiomAudit.lean`.

Every constant defined in a `ProjectEpisteme` module may depend only on Lean's standard axioms.
A `sorry` appears as the axiom `sorryAx`, and a project `axiom` declaration appears as itself,
so both fail the audit. The `#guard_msgs` blocks in each module pin the same result for
individual source items; this audit also covers declarations without such a block.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut categoryCount : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := modules[idx.toNat]!
    if (`ProjectEpisteme).isPrefixOf modName then
      count := count + 1
      if (`ProjectEpisteme.Category).isPrefixOf modName then
        categoryCount := categoryCount + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  unless count > 0 ∧ categoryCount > 0 do
    throwError "Audit found no project or Category-track declarations"
  logInfo m!"Axiom audit passed for {count} project declarations, including {categoryCount} Category-track declarations."
