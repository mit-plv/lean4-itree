import CTree.Par

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

namespace Paco
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

  private def mp (p : P) (pq : P → Q) : Q := pq p

  macro "pcofix_set_mark" : tactic => `(tactic|(
    apply mp paco_mark.mk_paco_mark
    intros
  ))

  elab "pcofix_intro_acc" : tactic =>
    Tactic.withMainContext do
      let goalType ← Tactic.getMainTarget
      let goalHead := goalType.getAppFn
      match goalHead with
      | .const c _ =>
        let expanded ← Meta.deltaExpand goalType (c == ·)
        unless expanded.isAppOf ``Lean.Order.lfp_monotone do
          throwError "{c} is not constructed with lfp_monotone"
        Tactic.liftMetaTactic fun mvarId => do
          return [← mvarId.replaceTargetDefEq expanded]
        let args := expanded.getAppArgs
        let plfp_acc ← Meta.mkConstWithFreshMVarLevels ``plfp_acc
        let mon := {name := `mon, val:= .expr args[3]!}
        let accBody ← Term.elabAppArgs plfp_acc #[mon] #[] none (explicit := true) false
        let accType ← Meta.inferType accBody
        let accName := (← getLCtx).getUnusedName `acc
        let markId := (← getLCtx).findDecl? λ decl =>
          match decl.type with
          | .const ``paco_mark _ => some decl.fvarId
          | _ => none
        let markId ← do
          match markId with
          | some id => pure id
          | none => throwError "unreachable"
        -- accType and accBody should not have dependencies below markId
        let (_, hasDep) := (← getLCtx).foldr (λ ldecl (found, hasDep) =>
          let fvar := ldecl.fvarId
          if found then (found, hasDep)
          else if fvar == markId then (true, hasDep)
          else (false, hasDep || accType.containsFVar fvar || accBody.containsFVar fvar)
        ) (false, false)
        if hasDep then
          throwError "plfp_acc should not depend on anything that is generalized"
        Tactic.liftMetaTactic fun mvarId => do
          let (_, mvarId) ← mvarId.revertAfter markId
          let mvarId ← mvarId.clear markId
          let mvarIdNew ← mvarId.assert accName accType accBody
          let (_, mvarIdNew) ← mvarIdNew.intro1P
          return [mvarIdNew]
        Tactic.evalTactic <| ← `(tactic|try rw [@plfp_init])
      | _ => throwError "{goalHead} is not a defined constant"

  def test := ∃ x, x = 1
  elab "pcofix_wrap" : tactic =>
    Tactic.withMainContext do
      let goalType ← Tactic.getMainTarget
      let (packer, packedGoalType, accArgType) ←
        Meta.forallTelescope goalType λ args conc => do
          let varNames ← args.mapM (·.fvarId!.getUserName)
          let packer : Meta.ArgsPacker := {varNamess := #[varNames]}
          let ty := conc.getAppArgs[0]!
          pure (packer, ← Meta.ArgsPacker.uncurryType packer #[goalType], ty)
      let funcExpr ← Meta.withLocalDecl `x BinderInfo.default packedGoalType λ x => do
        let body ← Meta.ArgsPacker.curry packer x
        Meta.mkLambdaFVars #[x] body
      let accArg ← Meta.forallTelescope accArgType λ accArgs _ => do
        Meta.forallTelescope packedGoalType λ packedArg goalConc => do
          let goalArgs := goalConc.getAppArgs[4:].toArray
          assert! (goalArgs.size == accArgs.size)
          let zipped := Array.zip accArgs goalArgs
          let anded ← Array.foldlM (λ (acc : Expr) (ab : Expr × Expr) => do
            let eq ← Meta.mkEq ab.1 ab.2
            pure (mkAnd eq acc)) (.const ``True []) zipped
          let exCtor ← Meta.mkConstWithFreshMVarLevels ``Exists
          let exType ← Meta.inferType packedArg[0]!
          let exBody ← Meta.mkLambdaFVars packedArg anded
          Meta.mkLambdaFVars accArgs (mkApp2 exCtor exType exBody)
      let accDecl := (← getLCtx).lastDecl
      let accId ← do
        match accDecl with
        | some decl => pure decl.fvarId
        | none => throwError "unreachable"
      Tactic.liftMetaTactic fun mvarId => do
        let mvarIds ← mvarId.apply funcExpr
        match mvarIds with
        | [mvarId] =>
          let (_, mvarId) ← mvarId.intros
          let mvarIds ← mvarId.apply (.app (.fvar accId) accArg) {}
          match mvarIds with
          | [mvarMain, mvarPf] =>
            let mvarMain ← mvarMain.cleanup
            let mvarMain ← mvarMain.clear accId
            return [mvarMain, mvarPf]
          | _ => throwError "unreachable"
        | _ => throwError "unreachable"
end Paco

namespace Lean.Expr
end Lean.Expr

namespace CTree
  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (t1 ◁ t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (t1 ▷ t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (t1 ◁▷ t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (t1 ⋈ t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (t1 ‖ₛ t2)) → IsParR t t1 t2

  namespace Euttc
    macro "crush_refine" : tactic => `(tactic|(
      repeat first
      | exact RefineF.ret rfl
      | exact RefineF.zero
      | apply RefineF.tau_left
      | apply RefineF.tau_right
      | apply RefineF.vis
      | apply RefineF.choice_idemp
      | apply RefineF.choice_idemp
      | apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
    ))

    macro "crush_parR_ret " c:term : tactic => `(tactic|(
      repeat apply And.intro rfl _
      exists $c
      apply And.intro _ rfl
      solve
      | exact IsParR.bothS rfl
      | exact IsParR.rS rfl
      | exact IsParR.parS rfl
    ))

    macro "parR_ret_left_lS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      all_goals
        intros; rename_i heq; subst heq
        simp only [parAux_lS_ret, map_zero]
        crush_refine
    ))

    macro "parR_ret_left_rS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      · intro y heq
        subst heq
        simp only [parAux_rS_ret_ret, map_zero]
        crush_refine
      · intro c heq
        subst heq
        simp only [parAux_rS_ret_tau, map_tau]
        crush_refine; crush_parR_ret c
      · intro α e k heq
        subst heq
        simp only [parAux_rS_ret_vis, map_vis]
        crush_refine; intro a
        crush_refine; crush_parR_ret k a
      · intro heq
        subst heq
        simp only [parAux_rS_ret_zero, map_zero]
        crush_refine
      · intro c1 c2 heq
        subst heq
        simp only [parAux_rS_ret_choice, map_choice]
        crush_refine
        · apply RefineF.choice_left
          crush_refine; crush_parR_ret c1
        · apply RefineF.choice_right
          crush_refine; crush_parR_ret c2
    ))

    theorem parR_ret_le : ((ret x) ‖→ t) ≤Eq≤ t := by
      apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, IsParR t1 (ret x) t ∧ t2 = t) _ 0 0
      · crush_parR_ret t
      · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
        subst hp1 hp2 ht2
        match ht1 with
        | .lS heq =>
          subst heq
          parR_ret_left_lS t2
        | .rS heq =>
          subst heq
          parR_ret_left_rS t2
        | .lrS heq =>
          subst heq
          simp only [parAux_lrS, map_choice]
          apply RefineF.choice_idemp
          · parR_ret_left_lS t2
          · parR_ret_left_rS t2
        | .bothS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_bothS_ret_ret, map_ret]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_bothS_ret_tau, map_tau]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_bothS_ret_vis, map_zero]
            crush_refine
          · intro heq
            subst heq
            simp only [parAux_bothS_ret_zero, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_bothS_ret_choice, map_choice]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
        | .parS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_parS_ret_ret, map_choice, map_ret, map_zero]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_parS_ret_tau, map_choice, map_tau, map_zero]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_parS_ret_vis, map_choice, map_zero, map_vis]
            crush_refine
            intro a
            crush_refine; crush_parR_ret k a
          · intro heq
            subst heq
            simp only [parAux_parS_ret_zero, map_choice, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_parS_ret_choice, map_choice, map_zero]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
            · crush_refine
              · apply RefineF.choice_left
                crush_refine; crush_parR_ret c1
              · apply RefineF.choice_right
                crush_refine; crush_parR_ret c2

    -- set_option pp.explicit true
    theorem le_parR_ret : t ≤Eq≤ ((ret (ρ := ρ) x) ‖→ t) := by
      exists 0, 0
      rename_i ε _
      revert t x
      pcofix_set_mark; pcofix_intro_acc; pcofix_wrap
      intro φ dummy cih
      clear dummy
      -- now we only have to rearrange (curry) cih and the goal
      on_goal 2 => rename_i x; exists x
      sorry

    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · exact parR_ret_le
      · rw [flip_eq]
        exact le_parR_ret

    macro "crush_parR_map_both_le " t1:term ", " t2:term : tactic => `(tactic|(
      repeat apply And.intro rfl _
      exists $t1, $t2
      try simp only [map_ret, and_self]
    ))

    macro "simp_parAux_bothS" : tactic => `(tactic|(
      simp only [
        parAux_bothS_ret_ret, parAux_bothS_ret_vis, parAux_bothS_ret_tau, parAux_bothS_ret_zero, parAux_bothS_ret_choice,
        parAux_bothS_vis_ret, parAux_bothS_vis_vis, parAux_bothS_vis_tau, parAux_bothS_vis_zero, parAux_bothS_vis_choice,
        parAux_bothS_tau_ret, parAux_bothS_tau_vis, parAux_bothS_tau_tau, parAux_bothS_tau_zero, parAux_bothS_tau_choice,
        parAux_bothS_zero_ret, parAux_bothS_zero_vis, parAux_bothS_zero_tau, parAux_bothS_zero_zero, parAux_bothS_zero_choice,
        parAux_bothS_choice_ret, parAux_bothS_choice_vis, parAux_bothS_choice_tau, parAux_bothS_choice_zero, parAux_bothS_choice_choice,
        map_vis, map_ret, map_tau, map_zero, map_choice
      ]
    ))

    open Lean

    macro "crush_match" t:term " with " simp_rule:tactic : tactic => `(tactic|(
      apply dMatchOn $t
      case' ret =>
        intro $(mkIdent `y) heq
        subst heq
      case' vis =>
        intro $(mkIdent `α2) $(mkIdent `e2) $(mkIdent `k2) heq
        subst heq
      case' tau =>
        intro $(mkIdent `t2) heq
        subst heq
      case' zero =>
        intro heq
        subst heq
      case' choice =>
        intro $(mkIdent `c21) $(mkIdent `c22) heq
        subst heq
      all_goals try ($simp_rule; crush_refine)
    ))

    theorem parR_map_both_le : map Prod.snd (parAux (map f t1 ⋈ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ⋈ t2)) := by
      apply Refine.coind
        (λ p1 p2 t1 t2 =>
          p1 = 0 ∧ p2 = 0 ∧ ∃ t1' t2', t1 = map Prod.snd (parAux (map f t1' ⋈ t2')) ∧ t2 = map Prod.snd (parAux (t1' ⋈ t2'))
        ) _ 0 0
      · crush_parR_map_both_le t1, t2
      · intro p1 p2 t1' t2' ⟨hp1, hp2, t1, t2, ht1, ht2⟩
        subst hp1 hp2 ht1 ht2
        apply dMatchOn t1
        · intro x heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le ret x, c21
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le ret x, c22
          · crush_parR_map_both_le ret x, t2
        · intro t1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · crush_parR_map_both_le t1, c21 ⊕ c22
          · crush_parR_map_both_le t1, zero
          · crush_parR_map_both_le t1, tau t2
          · crush_parR_map_both_le t1, vis e2 k2
          · crush_parR_map_both_le t1, ret y
        · intro α1 e1 k1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          all_goals rw [←map_vis (e := e1) (k := k1) (f := f)]
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le vis e1 k1, c21
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le vis e1 k1, c22
          · crush_parR_map_both_le vis e1 k1, t2
        · intro heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le zero, c21
            simp only [map_zero, and_self]
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le zero, c22
            simp only [map_zero, and_self]
          · crush_parR_map_both_le zero, t2
            simp only [map_zero, and_self]
        · intro c11 c12 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, c21 ⊕ c22
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, c21 ⊕ c22
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, zero
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, zero
          · rw [←map_choice (c1 := c11) (c2 := c12) (f := f)]
            crush_parR_map_both_le c11 ⊕ c12, t2
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, vis e2 k2
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, vis e2 k2
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, ret y
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, ret y

    -- theorem parR_map_lS_le : map Prod.snd (parAux (map f t1 ◁ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ◁ t2)) := by
    --   apply Refine.coind
    --     (λ p1 p2 t1 t2 =>
    --       p1 = 0 ∧ p2 = 0 ∧ ∃ t1' t2', t1 = map Prod.snd (parAux (map f t1' ◁ t2')) ∧ t2 = map Prod.snd (parAux (t1' ◁ t2'))
    --     ) _ 0 0
    --   · repeat apply And.intro rfl _
    --     exists t1, t2
    --   · intro p1 p2 t1' t2' ⟨hp1, hp2, t1, t2, ht1, ht2⟩
    --     subst hp1 hp2 ht1 ht2
    --     apply dMatchOn t1
    --     case vis =>
    --       intro α e k heq
    --       subst heq
    --       simp only [parAux_lS_vis, map_vis]
    --       crush_refine
    --       intro a
    --       -- TODO: this cannot be separated out into a separate lemma. Need to prove this with in the greater par lemma.
    --       sorry
    --     all_goals sorry

    -- theorem parR_map_rS_le : map Prod.snd (parAux (map f t1 ▷ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ▷ t2)) := by
    --   sorry

    -- theorem parR_map_lrS_le : map Prod.snd (parAux (map f t1 ◁▷ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ◁▷ t2)) := by
    --   simp only [parAux_lrS, map_choice]
    --   apply Refine.choice_idemp
    --   · apply Refine.choice_left
    --     exact parR_map_lS_le
    --   · apply Refine.choice_right
    --     exact parR_map_rS_le

    theorem parR_map_le : ((map f t1) ‖→ t2) ≤Eq≤ (t1 ‖→ t2) := by
      simp only [parR, par, Functor.map, parAux_parS, map_choice]
      sorry
      -- apply Refine.choice_idemp
      -- · apply Refine.choice_left
      --   exact parR_map_both_le
      -- · apply Refine.choice_right
      --   exact parR_map_lrS_le

    theorem le_parR_map : (t1 ‖→ t2) ≤Eq≤ ((map f t1) ‖→ t2) := by
      simp only [parR, par, Functor.map, parAux_parS, map_choice]
      sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      apply And.intro
      · exact parR_map_le
      · rw [flip_eq]
        exact le_parR_map

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
