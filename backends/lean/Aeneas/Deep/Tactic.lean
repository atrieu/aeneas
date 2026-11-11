module
public import Lean
public import Aeneas.Deep.Basic
public section

/-! # Tactics for the denotation theorems of deep terms -/

namespace Aeneas.Deep

open Lean Meta Elab Tactic

/-- Close a goal `lhs = rhs` with `Eq.refl lhs`, leaving the definitional equality check
entirely to the kernel.

This is the tactic used by the generated denotation theorems. The kernel check is linear
in the size of the term, while `Meta.isDefEq` is superlinear and refuses to unfold matcher
applications stuck on a variable. The price is that a failure is reported as a bare kernel
error: use `deep_rfl_meta` to get the usual goal display when debugging. -/
elab "deep_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := t.eq? | throwError "deep_rfl: expected an equality, got{indentExpr t}"
  goal.assign (← mkEqRefl lhs)
  replaceMainGoal []

/-- The matcher auxiliary definitions (`f.match_1`, …) occurring in `e`. -/
meta def collectMatchers (e : Lean.Expr) : MetaM (Array Name) := do
  let mut matchers := #[]
  for n in e.getUsedConstants do
    if (← getMatcherInfo? n).isSome then matchers := matchers.push n
  return matchers

/-- Close a goal `lhs = rhs` by `Meta.isDefEq`, after delta-expanding the matcher
applications of the goal.

`isDefEq` never delta-expands a matcher application whose discriminant is not a
constructor (see `Lean.Meta.unfoldDefinition?`), so a shallow `match` stuck on a variable
can not be compared with the `casesOn` application produced by the deep eliminator.
Expanding the matchers first solves this; everything else is handled by the usual
definitional unfolding. Slower than `deep_rfl`, but failures show the two sides. -/
elab "deep_rfl_meta" : tactic => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let matchers ← collectMatchers t
  let goal ← if matchers.isEmpty then pure goal else goal.deltaTarget (matchers.contains ·)
  goal.refl
  replaceMainGoal []

end Aeneas.Deep
