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
    let hypHead ← instantiateMVars hypType.consumeMData
    unless hypHead.isAppOf ``uplfp do
      throwError "{hypHead} is not uplfp"
    let rArg := hypHead.getAppArgs[4]!
    let uplfpHead ← Meta.mkAppOptM ``uplfp <| hypHead.getAppArgs[:5].toArray.map some
    let plfpHead ← Meta.mkAppOptM ``plfp <| hypHead.getAppArgs[:5].toArray.map some
    let head ← Meta.forallTelescope (← Meta.inferType rArg) λ args _ => do
      let plfpBody := mkAppN plfpHead args
      let rBody := mkAppN rArg args
      Meta.mkLambdaFVars args (mkOr rBody plfpBody) -- λ x, ⊤ₚ x ∨ plfp f x
    Tactic.liftMetaTactic λ mvarId => do
      let cola := hypHead.getAppArgs[1]!
      let porder ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.toPartialOrder #[none, some cola]
      let rel ← Meta.mkAppOptM ``Lean.Order.PartialOrder.rel #[none, porder]
      let le := mkApp2 rel head uplfpHead
      let (splitGoal, mvarId) ← mvarId.intro_fact_with_new_goal le
      let (_, mvarId) ← mvarId.intro1
      return [splitGoal, mvarId]
    Tactic.withoutRecover <| Tactic.evalTactic <| ← `(tactic|(
      simp only [uplfp, Lean.Order.CompleteLattice.meet_spec]
      apply And.intro <;>
      simp only [
        Lean.Order.instCompleteLatticePi,
        Lean.Order.instOrderPi,
        Lean.Order.ReverseImplicationOrder,
        Lean.Order.ReverseImplicationOrder.instCompleteLattice,
        Lean.Order.ReverseImplicationOrder.instOrder
      ] <;> solve
      | intros; left; assumption
      | intros; right; assumption
      rename_i h'; simp only [
        Lean.Order.instCompleteLatticePi,
        Lean.Order.instOrderPi,
        Lean.Order.ReverseImplicationOrder,
        Lean.Order.ReverseImplicationOrder.instCompleteLattice,
        Lean.Order.ReverseImplicationOrder.instOrder
      ] at h'
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
    let args := hypType.cleanupAnnotations.getAppArgs[5:]
    let applied := mkAppN (.fvar lastId) args
    let applied := mkApp applied (.fvar hyp)
    Tactic.liftMetaTactic λ mvarId => do
      let mvarId ← mvarId.intro_fact applied
      let (_, mvarId) ← mvarId.intro h.getId
      let mvarId ← mvarId.clear lastId
      let mvarId ← mvarId.clear hyp
      return [mvarId]

-- rewrites (uplfp f r) into (r ∨ plfp f r)
syntax "pcases" " at " ident : tactic
macro_rules
| `(tactic| pcases at $h:ident) =>
  `(tactic| pcases_prepare at $h:ident; pcases_do at $h:ident)

elab "pmon" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    unless goalType.isAppOf ``plfp do
      throwError "{goalType} is not plfp"
    let cola := goalType.getAppArgs[1]!
    let monArg := goalType.getAppArgs[3]!
    let monHead ← Meta.mkAppOptM ``plfp_mon <| #[none, cola, none, monArg]
    Tactic.liftMetaTactic λ mvarId => do
      let mvarIds ← mvarId.apply monHead
      return mvarIds

elab "ptop" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalType := goalType.cleanupAnnotations
    unless goalType.isAppOf ``Lean.Order.PartialOrder.rel do
      throwError "{goalType} is not partial order"
    let topArg := goalType.getAppArgs[3]!.cleanupAnnotations
    unless topArg.isAppOf ``Lean.Order.CompleteLattice.top do
      throwError "{goalType} is not CompleteLattice.top_spec"
    let cola := topArg.getAppArgs[1]!
    let le_top ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.top_spec <| #[none, cola]
    Tactic.liftMetaTactic λ mvarId => do
      let mvarIds ← mvarId.apply le_top
      return mvarIds
