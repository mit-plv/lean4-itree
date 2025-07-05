import CTree.PacoDefs

namespace Lean.Order.CompleteLattice
  notation "⊤ₚ" => top -- avoid clashing with Mathlib
end Lean.Order.CompleteLattice

open Lean Lean.Elab

elab "pcases_prepare" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some hypType := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.type
      else none) | throwError "Cannot find hypothesis of name {h.getId}"
    let hypType ← instantiateMVars hypType
    let hypHead := hypType.consumeMData.getAppFn.consumeMData
    unless hypHead.isAppOf ``uplfp do
      throwError "{hypHead} is not uplfp"
    let rArg := hypHead.getAppArgs[4]!
    let plfpHead ← Meta.mkAppOptM ``plfp <| hypHead.getAppArgs[:5].toArray.map some
    let head ← Meta.forallTelescope (← Meta.inferType rArg) λ args _ => do
      let plfpBody := mkAppN plfpHead args
      let rBody := mkAppN rArg args
      Meta.mkLambdaFVars args (mkOr rBody plfpBody)
    Tactic.liftMetaTactic λ mvarId => do
      let cola := hypHead.getAppArgs[1]!
      let porder ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.toPartialOrder #[none, some cola]
      let rel ← Meta.mkAppOptM ``Lean.Order.PartialOrder.rel #[none, porder]
      let le := mkApp2 rel head hypHead
      let (splitGoal, mvarId) ← mvarId.intro_fact_with_new_goal le
      let (_, mvarId) ← mvarId.intro1
      return [splitGoal, mvarId]
    Tactic.evalTactic <| ← `(tactic|(
      simp only [uplfp, Lean.Order.CompleteLattice.meet_spec]
      apply And.intro <;> solve
      | intros; left; assumption
      | intros; right; assumption
    ))

elab "pcases_do" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some last := (← getLCtx).lastDecl | throwError "unreachable"
    let lastId := last.fvarId
    let some hyp := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.fvarId
      else none) | throwError "unreachable"
    let hypType ← hyp.getType
    let hypType ← instantiateMVars hypType
    let args := hypType.consumeMData.getAppArgs
    let applied := mkAppN (.fvar lastId) args
    let applied := mkApp applied (.fvar hyp)
    Tactic.liftMetaTactic λ mvarId => do
      let mvarId ← mvarId.intro_fact applied
      let mvarId ← mvarId.clear lastId
      let mvarId ← mvarId.clear hyp
      let (_, mvarId) ← mvarId.intro h.getId
      return [mvarId]

-- rewrites (uplfp f r) into (r ∨ plfp f r)
syntax "pcases" " at " ident : tactic
macro_rules
| `(tactic| pcases at $h:ident) =>
  `(tactic| pcases_prepare at $h:ident; pcases_do at $h:ident)
