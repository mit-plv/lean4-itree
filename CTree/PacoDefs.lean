import Lean.Meta
import Lean.Elab

namespace Lean.Order.CompleteLattice
  open PartialOrder
  -- \meet
  instance [CompleteLattice α] : Min α where
    min x y := inf (λ z => z = x ∨ z = y)

  def top [CompleteLattice α] : α := sup (λ _ => True)

  scoped notation "⊤" => top
  scoped infixl:60 " ⊓ " => min

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
end Lean.Order.CompleteLattice

open Lean.Order PartialOrder CompleteLattice

-- note that we don't require monotonicity for f
-- this is the version in paco
theorem monotonize_mon [Lean.Order.CompleteLattice α] (f : α → α) r :
  monotone (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ x ⊑ y)) := by
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

theorem plfp_arg_mon [Lean.Order.CompleteLattice α] {f : α → α} (mon : monotone f) r :
  monotone (λ x => f (r ⊓ x)) := by
  simp only [monotone]
  intros
  apply mon
  rw [meet_spec]
  apply And.intro
  · apply meet_le_left; apply rel_refl
  · apply meet_le_right; assumption

-- parameterized least fixed point, we don't "monotonize" f (⌈f⌉) as in paco for now
-- version in paco: lfp (λ x => inf (fun z => ∃ y, z = f y ∧ r ⊓ x ⊑ y)
def plfp [Lean.Order.CompleteLattice α] (f : α → α) {mon} r :=
  lfp_monotone (λ x => f (r ⊓ x)) (plfp_arg_mon mon r)

-- "unfolded" plfp, r ⊓ plfp f r
def uplfp [Lean.Order.CompleteLattice α] (f : α → α) {mon} r :=
  r ⊓ (plfp f (mon := mon) r)

theorem plfp_mon [Lean.Order.CompleteLattice α] {f : α → α} mon :
  monotone (plfp f (mon := mon)) := by
  simp only [monotone, plfp]
  intros
  apply le_sup; intros; apply Lean.Order.sup_le; intros
  rename_i h; apply h
  rename_i h' _; apply rel_trans _ h'; simp only; apply mon
  rw [meet_spec]; apply And.intro
  · apply rel_trans _ (by assumption)
    apply meet_le_left; apply rel_refl
  · apply meet_le_right; apply rel_refl

theorem plfp_init [Lean.Order.CompleteLattice α] {f : α → α} mon :
  lfp_monotone f mon = plfp f (mon := mon) ⊤ := by
  apply rel_antisymm <;>
  (apply le_sup; intros; apply Lean.Order.sup_le; intros; rename_i h; apply h) <;>
  (rename_i h' _; apply rel_trans _ h'; simp only) <;>
  (rw [meet_comm, meet_top]; apply rel_refl)

theorem plfp_unfold [Lean.Order.CompleteLattice α] {f : α → α} mon :
  plfp f (mon := mon) r = f (uplfp f (mon := mon) r) := by
  rw [plfp]
  delta lfp_monotone
  rw [lfp_fix]
  rw [← lfp_monotone]
  rw [← plfp]
  · rfl
  · apply plfp_arg_mon mon

theorem uplfp_goal [Lean.Order.CompleteLattice α] {f : α → α} mon :
  r ⊑ z ∨ plfp f (mon := mon) r ⊑ z → uplfp (mon := mon) f r ⊑ z := by
  simp only [uplfp]
  intro h; cases h
  · apply meet_le_left; assumption
  · apply meet_le_right; assumption

theorem uplfp_hyp [Lean.Order.CompleteLattice α] {f : α → α} mon :
  z ⊑ uplfp (mon := mon) f r → z ⊑ r ∧ z ⊑ plfp f (mon := mon) r := by
  simp only [uplfp]
  rw [meet_spec]
  exact id

theorem plfp_acc_aux [Lean.Order.CompleteLattice α] {f : α → α} mon r x :
  plfp f (mon := mon) r ⊑ x ↔ plfp f (mon := mon) (r ⊓ x) ⊑ x := by
  constructor <;> (intro h; apply rel_trans _ h)
  · apply plfp_mon mon; exact meet_le_left _ rel_refl
  · apply lfp_le_of_le
    apply rel_trans _ (by rw [plfp_unfold]; apply rel_refl)
    apply mon
    rw [uplfp, meet_spec]
    apply And.intro
    · rw [meet_spec]
      exact And.intro (meet_le_left _ rel_refl) (meet_le_right _ h)
    · exact meet_le_right _ rel_refl

theorem plfp_acc [Lean.Order.CompleteLattice α] {f : α → α} mon l r
  (obg : ∀ φ, φ ⊑ r → φ ⊑ l → plfp f (mon := mon) φ ⊑ l) : plfp f (mon := mon) r ⊑ l := by
  rw [plfp_acc_aux mon]
  apply obg
  · apply meet_le_left _ rel_refl
  · apply meet_le_right _ rel_refl

-- tactics
open Lean Lean.Elab

private inductive paco_mark : Prop
| mk_paco_mark

-- modus ponens, used to introduce new hypothesis
private def mp P Q (p : P) (pq : P → Q) : Q := pq p

-- introduce a new fact, given the witness for that fact
def Lean.MVarId.intro_fact (mvarId : MVarId) (fact : Expr) : MetaM MVarId := do
  let mp ← Meta.mkAppM ``mp #[(← Meta.inferType fact), (← mvarId.getType), fact]
  let [mvarId] ← mvarId.apply mp | throwError "unreachable"
  return mvarId

-- introduce a new fact, and a new goal to prove that fact
-- the new goal is the first return value
def Lean.MVarId.intro_fact_with_new_goal (mvarId : MVarId) (factType : Expr) : MetaM (MVarId × MVarId) := do
  let mp ← Meta.mkAppM ``mp #[factType, (← mvarId.getType)]
  let [factId, mvarId] ← mvarId.apply mp | throwError "unreachable"
  return (factId, mvarId)

elab "pinit" : tactic =>
  Tactic.liftMetaTactic λ mvarId => do
    let mark := Expr.const ``paco_mark.mk_paco_mark []
    let mvarId ← mvarId.intro_fact mark
    let originalHypNum := Meta.getIntrosSize (← mvarId.getType)
    let (_, mvarId) ← mvarId.introNP originalHypNum
    let goalType ← mvarId.getType
    let goalHead := goalType.getAppFn
    let Expr.const c _ := goalHead | throwError "{goalHead} is not a defined constant"
    let expanded ← Meta.deltaExpand goalType (c == ·)
    unless expanded.isAppOf ``Lean.Order.lfp_monotone do
      throwError "{expanded} is not constructed with lfp_monotone"
    -- unfold all instances of the predicate, even in the context
    let mvarId ← mvarId.revertAll
    let revertedHypNum := Meta.getIntrosSize (← mvarId.getType)
    let mvarId ← mvarId.deltaTarget (c == ·)
    let (_, mvarId) ← mvarId.introNP revertedHypNum
    return [mvarId]

elab "pcofix_intro_acc" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    let monArg := goalType.getAppArgs[3]!
    let plfp_acc ← Meta.mkConstWithFreshMVarLevels ``plfp_acc
    let mon := {name := `mon, val:= .expr monArg}
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
      else (false, hasDep || monArg.containsFVar fvar)
    ) (false, false)
    if hasDep then
      throwError "{monArg}, the proof of monotonicity should not depend on anything that is generalized"
    Tactic.liftMetaTactic fun mvarId => do
      let (_, mvarId) ← mvarId.revertAfter markId
      let mvarId ← mvarId.clear markId
      let mvarId ← mvarId.intro_fact accBody
      let (_, mvarId) ← mvarId.intro1
      return [mvarId]

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
        let goalArgs := goalConc.getAppArgs[5:].toArray
        if goalArgs.size != accArgs.size then
          throwError "pcofix_wrap, {goalArgs} and {accArgs} have different length"
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
      let mvarMain ← mvarMain.intro_fact unpacker
      let (converter, mvarMain) ← mvarMain.intro_fact_with_new_goal converter
      return [mvarPf, converter, mvarMain]

elab "destruct_last_and" : tactic =>
  Tactic.liftMetaTactic fun mvarId => do
    let some last := (← getLCtx).lastDecl | throwError "unreachable"
    let lastId := last.fvarId
    let lastType ← lastId.getType
    unless lastType.isAppOf ``And do
      throwError "constructor is not and"
    let left ← Meta.mkAppM ``And.left #[.fvar lastId]
    let right ← Meta.mkAppM ``And.right #[.fvar lastId]
    let mvarId ← mvarId.intro_fact left
    let (_, mvarId) ← mvarId.intro1
    let mvarId ← mvarId.intro_fact right
    let (_, mvarId) ← mvarId.intro1
    let mvarId ← mvarId.clear lastId
    return [mvarId]

macro "pcofix" : tactic => `(tactic|(
  pinit; rw [@plfp_init] at *; pcofix_intro_acc; pcofix_wrap
  rename_i x; exists x -- proof for plfp_acc
  intros; constructor -- proof for converter
  · intro h x; apply h; exists x
  · intro h; intros; rename_i anded; revert anded; intro ⟨_, anded⟩
    repeat (destruct_last_and; rename_i h' _; subst h')
    apply h; try assumption
  intro converter unpacker φ dummy cih -- main goal
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

elab "pinit" " at " h:ident : tactic =>
  Tactic.withMainContext do
    let some hyp := (← getLCtx).findDecl? (λ ldecl =>
      if ldecl.userName == h.getId then some ldecl.fvarId
      else none) | throwError "Cannot find hypothesis of name {h.getId}"
    let hypType ← hyp.getType
    let hypHead := hypType.getAppFn
    let Expr.const c _ := hypHead | throwError "{hypHead} is not a defined constant"
    let expanded ← Meta.deltaExpand hypType (c == ·)
    unless expanded.isAppOf ``Lean.Order.lfp_monotone do
      throwError "{expanded} is not constructed with lfp_monotone"
    Tactic.liftMetaTactic λ mvarId => do
      let originalHypNum := Meta.getIntrosSize (← mvarId.getType)
      let mvarId ← mvarId.revertAll
      let revertedHypNum := Meta.getIntrosSize (← mvarId.getType)
      -- unfold all instances of the predicate, even in the context
      let mvarId ← mvarId.deltaTarget (c == ·)
      let (_, mvarId) ← mvarId.introNP (revertedHypNum - originalHypNum)
      return [mvarId]
    Tactic.evalTactic <| ← `(tactic|rw [@plfp_init] at *)

syntax "pclearbot" " at " ident : tactic
macro_rules
| `(tactic| pclearbot at $h:ident) =>
  `(tactic|
      simp only [uplfp] at $h:ident;
      rw [@Lean.Order.CompleteLattice.meet_comm, @Lean.Order.CompleteLattice.meet_top] at $h:ident)

elab "split_uplfp" : tactic =>
  Tactic.withMainContext do
    let goalType ← Tactic.getMainTarget
    unless goalType.isAppOf ``uplfp do
      throwError "not uplfp"
    let monArg := goalType.getAppArgs[3]!
    let uplfp_goal ← Meta.mkConstWithFreshMVarLevels ``uplfp_goal
    let mon := {name := `mon, val:= .expr monArg}
    let body ← Term.elabAppArgs uplfp_goal #[mon] #[] none (explicit := true) false
    Tactic.liftMetaTactic fun mvarId => do
      let mvarId ← mvarId.intro_fact body
      return [mvarId]
    Tactic.evalTactic <| ← `(tactic|
      intro _uplfp_goal;
      simp only [
        Lean.Order.instCompleteLatticePi,
        Lean.Order.instOrderPi,
        Lean.Order.ReverseImplicationOrder,
        Lean.Order.ReverseImplicationOrder.instCompleteLattice,
        Lean.Order.ReverseImplicationOrder.instOrder
      ] at _uplfp_goal;
      apply _uplfp_goal)
