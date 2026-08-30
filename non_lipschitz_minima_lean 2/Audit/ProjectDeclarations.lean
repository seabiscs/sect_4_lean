import StressTensor
import Mathlib.Util.PrintSorries

open Lean Elab Command

/- Fail compilation if the imported project namespace contains a custom axiom
declaration or if any project declaration depends on a Lean proof placeholder.
This checks the elaborated environment rather than relying on text search. -/
run_cmd do
  let env ← getEnv
  let mut projectDecls := 0
  let mut projectNames : Array Name := #[]
  let mut projectAxioms : Array Name := #[]
  for (name, info) in env.constants.map₁ do
    if `StressTensor |>.isPrefixOf name then
      projectDecls := projectDecls + 1
      projectNames := projectNames.push name
      if info matches .axiomInfo _ then
        projectAxioms := projectAxioms.push name
  unless projectAxioms.isEmpty do
    throwError m!"project-defined axioms found: {projectAxioms}"
  let sorries ← liftTermElabM <| Mathlib.PrintSorries.collectSorries projectNames
  unless sorries.isEmpty do
    throwError m!"project declarations depend on proof placeholders: {sorries}"
  logInfo m!"checked {projectDecls} StressTensor declarations: no project-defined axioms or proof placeholders"
