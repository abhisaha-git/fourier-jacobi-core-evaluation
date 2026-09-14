import Lean

/-!
Compare compiled Palomar statements in separate Lean environments.

The traversal follows Comparator's statement-dependency comparison at
575674928e239f5bc452aab72d1dd7b0f1326494:
https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Comparator/Compare.lean

Selected theorem bodies are deliberately excluded. Every declaration used in
their types is compared, recursively including definition bodies and inductive
dependencies. This check is stricter about expression metadata than the export
comparison. It supplements the existing proof audits; it does not run protected
Comparator, independent NanoDa replay, or Palomar editorial review.

Run after building Challenge and Solution:
  lake env lean --run scripts/check-palomar-statements.lean
-/

open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

private def declarationDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut names := info.type.getUsedConstants.push info.name
  if let some value := info.value? (allowOpaque := true) then
    names := names ++ value.getUsedConstants
  match info with
  | .inductInfo value => names := names ++ value.ctors.toArray ++ value.all.toArray
  | .ctorInfo value => names := names.push value.induct
  | .recInfo value =>
    for rule in value.rules do
      names := (names.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return names

private def lookup (env : Environment) (name : Name) (side : String) : IO ConstantInfo :=
  match env.find? name with
  | some info => pure info
  | none => throw <| IO.userError s!"Missing {side} declaration: {name}"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (args.headD "comparator.json"))
  let challengeModule ← IO.ofExcept <| config.getObjValAs? String "challenge_module"
  let solutionModule ← IO.ofExcept <| config.getObjValAs? String "solution_module"
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let targets := names.map String.toName
  let holes := (config.getObjValAs? (Array String) "definition_names").toOption.getD #[]
  unless holes.isEmpty do
    throw <| IO.userError "This package check expects concrete definitions without definition holes"
  unless !targets.isEmpty do
    throw <| IO.userError "The Comparator configuration must select at least one theorem"
  let challenge ← importModules #[{ module := challengeModule.toName }] {}
  let solution ← importModules #[{ module := solutionModule.toName }] {}
  if solution.header.moduleNames.contains challengeModule.toName then
    throw <| IO.userError "Solution must not import the statement template"
  let mut worklist : Array Name := #[]
  for target in targets do
    let .thmInfo cc ← lookup challenge target "Challenge"
      | throw <| IO.userError s!"Challenge target is not a theorem: {target}"
    let .thmInfo sc ← lookup solution target "Solution"
      | throw <| IO.userError s!"Solution target is not a theorem: {target}"
    unless cc.toConstantVal == sc.toConstantVal do
      throw <| IO.userError s!"Compiled theorem types do not match: {target}"
    worklist := worklist ++ cc.type.getUsedConstants
  let mut checked : Std.HashSet Name := {}
  while !worklist.isEmpty do
    let target := worklist.back!
    worklist := worklist.pop
    unless checked.contains target do
      let cc ← lookup challenge target "Challenge"
      let sc ← lookup solution target "Solution"
      if targets.contains target then
        worklist := worklist ++ sc.type.getUsedConstants
      else
        unless cc == sc do
          throw <| IO.userError s!"Compiled statement dependency does not match: {target}"
        worklist := worklist ++ declarationDependencies sc
      checked := checked.insert target
  IO.println s!"PASS: {targets.size} compiled theorem types and {checked.size} transitive statement dependencies match exactly."
  IO.println "Selected theorem bodies were excluded; run the proof audits and Palomar verification separately."
