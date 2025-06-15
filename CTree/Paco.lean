import Mathlib.Data.Rel

namespace Lean.Order
  open PartialOrder CompleteLattice
  -- \meet
  instance [CompleteLattice α] : Min α where
    min x y := inf (λ z => z = x ∨ z = y)

  instance [CompleteLattice α] : Top α where
    top := sup (λ _ => True)

  theorem top_spec [CompleteLattice α] (x : α) : x ⊑ ⊤ := by
    apply le_sup; constructor

  theorem meet_spec [CompleteLattice α] (x y : α) : z ⊑ x ⊓ y ↔ z ⊑ x ∧ z ⊑ y := by
    constructor <;> simp only [min, inf_spec]
    · intro h
      exact And.intro (h _ <| Or.intro_left _ rfl) <| (h _ <| Or.intro_right _ rfl)
    · intro ⟨hx, hy⟩
      intros; rename_i h
      cases h <;> (rename_i h; subst h; assumption)

  theorem meet_le_left [CompleteLattice α] (x : α) : x ⊑ z → x ⊓ y ⊑ z := by
    simp only [min, inf_spec]
    intros
    apply rel_trans _ (by assumption)
    apply sup_le
    intros; rename_i h; apply h; left; rfl

  theorem meet_le_right [CompleteLattice α] (y : α) : y ⊑ z → x ⊓ y ⊑ z := by
    simp only [min, inf_spec]
    intros
    apply rel_trans _ (by assumption)
    apply sup_le
    intros; rename_i h; apply h; right; rfl

  theorem meet_top [CompleteLattice α] (x : α) : x ⊓ ⊤ = x := by
    apply rel_antisymm
    · exact meet_le_left _ rel_refl
    · rw [meet_spec]; apply And.intro rel_refl (top_spec _)

  theorem meet_comm [CompleteLattice α] (x y : α) : x ⊓ y = y ⊓ x := by
    apply rel_antisymm <;> (rw [meet_spec]; apply And.intro)
    all_goals solve
      | apply meet_le_left; apply rel_refl
      | apply meet_le_right; apply rel_refl

  theorem meet_assoc [CompleteLattice α] (x y z : α) : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
    apply rel_antisymm <;> (rw [meet_spec]; apply And.intro)
    · apply meet_le_left; apply meet_le_left; apply rel_refl
    · rw [meet_spec]; apply And.intro
      · apply meet_le_left; apply meet_le_right; apply rel_refl
      · apply meet_le_right; apply rel_refl
    · rw [meet_spec]; apply And.intro
      · apply meet_le_left; apply rel_refl
      · apply meet_le_right; apply meet_le_left; apply rel_refl
    · apply meet_le_right; apply meet_le_right; apply rel_refl
end Lean.Order

open Lean.Order PartialOrder CompleteLattice

-- typeclass to register hints for monotonicity
class PacoMon [Lean.Order.PartialOrder α] (f : α → α)
where
  mon : monotone f

-- parametric least fixed point, we don't "monotonize" f (⌈f⌉) as in paco for now
-- version in paco: lfp (λ x => inf (fun z => ∃ y, z = f y ∧ r ⊓ x ⊑ y)
def plfp [Lean.Order.CompleteLattice α] (f : α → α) r :=
  lfp (λ x => f (r ⊓ x))

-- "unfolded" plfp, r ⊓ plfp f r
def uplfp [Lean.Order.CompleteLattice α] (f : α → α) r :=
  r ⊓ (plfp f r)

-- note that we don't require monotonicity for f
-- this is the version in paco
instance [Lean.Order.CompleteLattice α] (f : α → α) r : PacoMon (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ x ⊑ y))
where
  mon := by
    simp only [monotone]
    intros _ _ h
    apply le_sup; intro z ⟨y, heq, h'⟩
    subst heq
    apply Lean.Order.sup_le; intro _ le
    apply le
    exists y; apply And.intro rfl
    apply rel_trans _ h'
    rw [meet_spec]
    apply And.intro
    · apply meet_le_left _ rel_refl
    · apply meet_le_right _ h

instance [Lean.Order.CompleteLattice α] (f : α → α) [PacoMon f] r : PacoMon (λ x => f (r ⊓ x))
where
  mon := by
    simp only [monotone]
    intros
    apply PacoMon.mon
    rw [meet_spec]
    apply And.intro
    · apply meet_le_left; apply rel_refl
    · apply meet_le_right; assumption

instance [Lean.Order.CompleteLattice α] (f : α → α) [PacoMon f] : PacoMon (plfp f)
where
  mon := by
    simp only [monotone, plfp]
    intros
    apply le_sup; intros; apply Lean.Order.sup_le; intros
    rename_i h; apply h
    rename_i h' _; apply rel_trans _ h'; apply PacoMon.mon
    rw [meet_spec]; apply And.intro
    · apply rel_trans _ (by assumption)
      apply meet_le_left; apply rel_refl
    · apply meet_le_right; apply rel_refl

theorem plfp_init_aux [Lean.Order.CompleteLattice α] (f : α → α) : lfp f = plfp f ⊤ := by
  apply rel_antisymm <;>
  (apply le_sup; intros; apply Lean.Order.sup_le; intros; rename_i h; apply h) <;>
  (rename_i h' _; apply rel_trans _ h'; simp only) <;>
  (rw [meet_comm, meet_top]; apply rel_refl)

theorem plfp_init [Lean.Order.CompleteLattice α] (f : α → α) {mon} : lfp_monotone f mon = plfp f ⊤ := by
  delta lfp_monotone
  apply plfp_init_aux

theorem plfp_unfold [Lean.Order.CompleteLattice α] (f : α → α) [PacoMon f] :
  plfp f r = f (uplfp f r) := by
  rw [plfp, lfp_fix]
  rw [← plfp]
  · rfl
  · apply PacoMon.mon

theorem plfp_acc_aux [Lean.Order.CompleteLattice α] (f : α → α) [mon : PacoMon f] r x :
  plfp f r ⊑ x ↔ plfp f (r ⊓ x) ⊑ x := by
  constructor <;> (intro h; apply rel_trans _ h)
  · apply PacoMon.mon; exact meet_le_left _ rel_refl
  · apply lfp_le_of_le
    apply rel_trans
    on_goal 2 => rw [plfp_unfold]; apply rel_refl
    apply PacoMon.mon
    rw [uplfp, meet_spec]
    apply And.intro
    · rw [meet_spec]
      exact And.intro (meet_le_left _ rel_refl) (meet_le_right _ h)
    · exact meet_le_right _ rel_refl

theorem plfp_acc [Lean.Order.CompleteLattice α] {f : α → α} (mon : monotone f) l r
  (obg : ∀ φ, φ ⊑ r → φ ⊑ l → plfp f φ ⊑ l) : plfp f r ⊑ l := by
  rw [plfp_acc_aux (mon := {mon := by assumption})]
  apply obg
  · apply meet_le_left _ rel_refl
  · apply meet_le_right _ rel_refl

-- tactics
open Lean Lean.Elab

private inductive paco_mark
| mk_paco_mark

private def mp P Q (p : P) (pq : P → Q) : Q := pq p

macro "pcofix_set_mark" : tactic => `(tactic|(
  apply mp _ _ paco_mark.mk_paco_mark
  intros
))

elab "pcofix_intro_acc" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let goalHead := goalType.getAppFn
    let Expr.const c _ := goalHead | throwError "{goalHead} is not a defined constant"
    let expanded ← Meta.deltaExpand goalType (c == ·)
    unless expanded.isAppOf ``Lean.Order.lfp_monotone do
      throwError "{c} is not constructed with lfp_monotone"
    Tactic.liftMetaTactic fun mvarId => do
      return [← mvarId.replaceTargetDefEq expanded]
    let monArg := expanded.getAppArgs[3]!
    let plfp_acc ← Meta.mkConstWithFreshMVarLevels ``plfp_acc
    let PacoMon ← Meta.mkConstWithFreshMVarLevels ``PacoMon.mk
    let mon := {name := `mon, val:= .expr monArg}
    let MonBody ← Term.elabAppArgs PacoMon #[mon] #[] none (explicit := true) false
    let accBody ← Term.elabAppArgs plfp_acc #[mon] #[] none (explicit := true) false
    let some markId := (← getLCtx).findDecl? (λ decl =>
      match decl.type with
      | .const ``paco_mark _ => some decl.fvarId
      | _ => none) | throwError "unreachable"
    -- accType and accBody should not have dependencies below markId
    let (_, hasDep) := (← getLCtx).foldr (λ ldecl (found, hasDep) =>
      let fvar := ldecl.fvarId
      if found then (found, hasDep)
      else if fvar == markId then (true, hasDep)
      else (false, hasDep || monArg.containsFVar fvar || monArg.containsFVar fvar)
    ) (false, false)
    if hasDep then
      throwError "{monArg}, the proof of monotonicity should not depend on anything that is generalized"
    Tactic.liftMetaTactic fun mvarId => do
      let (_, mvarId) ← mvarId.revertAfter markId
      let mvarId ← mvarId.clear markId
      let mp ← Meta.mkAppM ``mp #[(← Meta.inferType accBody), (← mvarId.getType), accBody]
      let [mvarId] ← mvarId.apply mp | throwError "unreachable"
      let mp ← Meta.mkAppM ``mp #[(← Meta.inferType MonBody), (← mvarId.getType), MonBody]
      let [mvarId] ← mvarId.apply mp | throwError "unreachable"
      let (_, mvarId) ← mvarId.introN 2
      return [mvarId]
    Tactic.evalTactic <| ← `(tactic|rw [@plfp_init])

elab "pcofix_wrap" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let (packer, packedGoalType, accArgType) ←
      Meta.forallTelescope goalType λ args conc => do
        let varNames ← args.mapM (·.fvarId!.getUserName)
        let packer : Meta.ArgsPacker := {varNamess := #[varNames]}
        let ty := conc.getAppArgs[0]!
        pure (packer, ← Meta.ArgsPacker.uncurryType packer #[goalType], ty)
    let toPacked ← Meta.withLocalDecl `x BinderInfo.default packedGoalType λ x => do
      let body ← Meta.ArgsPacker.curry packer x
      Meta.mkLambdaFVars #[x] body
    let (accArg, unpacker, converter) ← Meta.forallTelescope accArgType λ accArgs _ => do
      Meta.forallTelescope packedGoalType λ packedArg goalConc => do
        let goalArgs := goalConc.getAppArgs[4:].toArray
        assert! (goalArgs.size == accArgs.size)
        let anded ← Array.foldlM (λ acc (accArg, goalArg) => do
          let eq ← Meta.mkEq accArg goalArg
          pure (mkAnd eq acc)
        ) (.const ``True []) (Array.zip accArgs goalArgs)
        let exBody ← Meta.mkLambdaFVars packedArg anded
        let ex ← Meta.mkAppM ``Exists #[exBody]
        let (unpacker, converter) ← Meta.withLocalDecl `φ BinderInfo.default accArgType λ φ => do
          let leftBody ← mkArrow ex (mkAppN φ accArgs)
          let left ← Meta.mkForallFVars accArgs leftBody
          let rightPacked ← Meta.mkForallFVars packedArg (mkAppN φ goalArgs)
          let right ← Meta.ArgsPacker.curryType packer rightPacked
          let toPacked ← Meta.withLocalDecl `f BinderInfo.default right[0]! λ f => do
            let body ← Meta.ArgsPacker.uncurry packer #[f]
            Meta.mkLambdaFVars #[f] body
          let toUnpacked ← Meta.withLocalDecl `f BinderInfo.default rightPacked λ f => do
            let body ← Meta.ArgsPacker.curry packer f
            Meta.mkLambdaFVars #[f] body
          let iffType ← Meta.inferType toUnpacked
          let some (a, b) := iffType.arrow? | throwError "unreachable"
          let iffIntro := Expr.const ``Iff.intro []
          let unpacker ← Meta.mkLambdaFVars #[φ] (mkApp4 iffIntro a b toUnpacked toPacked)
          let converter ← Meta.mkForallFVars #[φ] (mkIff left rightPacked)
          pure (unpacker, converter)
        let accArg ← Meta.mkLambdaFVars accArgs ex
        pure (accArg, unpacker, converter)
    let some accDecl := (← getLCtx).lastDecl | throwError "unreachable"
    let accId := accDecl.fvarId
    Tactic.liftMetaTactic fun mvarId => do
      let [mvarId] ← mvarId.apply toPacked | throwError "unreachable"
      let (_, mvarId) ← mvarId.intros
      let [mvarMain, mvarPf] ← mvarId.apply (.app (.fvar accId) accArg) {} | throwError "unreachable"
      let mvarMain ← mvarMain.cleanup
      let mvarMain ← mvarMain.clear accId
      let mp ← Meta.mkAppM ``mp #[(← Meta.inferType unpacker), (← mvarMain.getType), unpacker]
      let [mvarMain] ← mvarMain.apply mp | throwError "unreachable"
      let mp ← Meta.mkAppM ``mp #[converter, (← mvarMain.getType)]
      let [converter, mvarMain] ← mvarMain.apply mp | throwError "unreachable"
      return [converter, mvarMain, mvarPf]

elab "destruct_last_and" : tactic =>
  Tactic.liftMetaTactic fun mvarId => do
    let some last := (← getLCtx).lastDecl | throwError "unreachable"
    let lastId := last.fvarId
    let #[case] ← mvarId.cases lastId | throwError "last hyp has many cases"
    if case.ctorName != ``And.intro then throwError "constructor is not and"
    return [case.mvarId]

elab "subst_all" : tactic =>
  Tactic.liftMetaTactic fun mvarId => do
    let some mvarId ← mvarId.substEqs | throwError "cannot subst"
    return [mvarId]

macro "pcofix" : tactic => `(tactic|(
  pcofix_set_mark; pcofix_intro_acc; pcofix_wrap
  on_goal 3 => rename_i x; exists x
  intros; constructor
  · intro h x; apply h; exists x
  · intro h; intros; rename_i anded; revert anded; intro ⟨_, anded⟩
    repeat destruct_last_and
    subst_all; apply h
  intro converter unpacker φ dummy cih
  simp only [
    Lean.Order.instCompleteLatticePi,
    Lean.Order.instOrderPi,
    Lean.Order.ReverseImplicationOrder,
    Lean.Order.ReverseImplicationOrder.instCompleteLattice,
    Lean.Order.ReverseImplicationOrder.instOrder
  ] at *
  rw [converter, unpacker] at *
  clear converter unpacker dummy
))

macro "pfold" : tactic => `(tactic|(rw [@plfp_unfold]))
syntax "punfold" " at " ident : tactic
macro_rules
| `(tactic| punfold at $h:ident) =>
  `(tactic| rw [@plfp_unfold] at $h:ident)
