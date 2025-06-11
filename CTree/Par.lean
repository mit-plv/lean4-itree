import CTree.Basic
import CTree.Monad
import CTree.Euttc
import Mathlib.Data.Vector3

namespace CTree
  /- Paralle Opeartor -/

  inductive ParState (ε : Type → Type) (α β : Type)
    | lS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ◁ ·
    | rS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ▷ ·
    | lrS (t1 : CTree ε α) (t2 : CTree ε β)   -- (· ◁ ·) ⊕ (· ▷ ·)
    | bothS (t1 : CTree ε α) (t2 : CTree ε β) -- · ⋈ ·
    | parS (t1 : CTree ε α) (t2 : CTree ε β)  -- · ‖ ·

  def parAux (ps : ParState ε α β) : CTree ε (α × β) :=
    corec' (λ {_} rec state =>
      match state with
      | .lS t1 t2 =>
        match t1.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| .lS (c _fin0) t2)
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .lS (cts _fin0) t2) (rec <| .lS (cts _fin1) t2)
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| .parS (k <| .up a) t2)
      | .rS t1 t2 =>
        match t2.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| .rS t1 (c _fin0))
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .rS t1 (cts _fin0)) (rec <| .rS t1 (cts _fin1))
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| .parS t1 (k {down := a}))
      | .lrS t1 t2 =>
        .inr <| choice' (rec <| .lS t1 t2) (rec <| .rS t1 t2)
      | .bothS t1 t2 =>
        match t1.dest, t2.dest with
        | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => .inl <| ret (x, y)
        | ⟨.tau, c⟩, _ => .inr <| tau' (rec <| .bothS (c _fin0) t2)
        | _, ⟨.tau, c⟩ => .inr <| tau' (rec <| .bothS t1 (c _fin0))
        | ⟨.choice, cts⟩, _ =>
          .inr <| choice' (rec <| .bothS (cts _fin0) t2) (rec <| .bothS (cts _fin1) t2)
        | _, ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .bothS t1 (cts _fin0)) (rec <| .bothS t1 (cts _fin1))
        | _, _ => .inl <| zero
      | .parS t1 t2 =>
        .inr <| choice' (rec <| .bothS t1 t2) (rec <| .lrS t1 t2)
    ) ps

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    parAux (.parS t1 t2)
  infixr:60 " ‖ " => par

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 ‖ t2)
  infixr:60 " ‖→ " => parR

  macro "simp_ctree_mk" : tactic => `(tactic|(
    simp only [
      mk, PFunctor.M.dest_mk,
      ret, ret',
      tau, tau',
      vis, vis',
      zero, zero',
      choice, choice',
    ]
  ))

  /--
  The least amount of theorems needed to unfold a `corec'` call to see the
  `PFunctor.M.mk` constructor.
  -/
  macro "simp_corec_base" : tactic => `(tactic|(
    simp_all (config := {maxSteps := 400000}) only [
      -- `corec`
      corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
      -- `map`
      PFunctor.map,
      -- Get rid of `Sum.bind`
      Bind.bind, Sum.bind
    ]
  ))

  macro "simp_corec_full" : tactic => `(tactic|(
    simp_all only [
      -- `PFunctor.M.corec` related
      corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
      -- Other `PFunctor` things
      PFunctor.map, PFunctor.map_eq, PFunctor.M.dest_mk, PFunctor.M.children_mk,
      -- Get rid of `Sum.bind` in `PFunctor.M.corec'`
      Bind.bind, Sum.bind,
      -- `CTree` constructors
      mk, ret, ret', vis, vis', tau, tau', zero, zero', choice, choice',
      -- General function things
      Function.comp_apply, Function.id_comp, id_eq,
      -- `Vector3` related
      Fin2.ofNat', _fin2Const, _fin1Const, _fin0, _fin1, Vector3.cons_fz, Vector3.cons_fs,
      -- `Nat` related
      Nat.reduceAdd,
      -- Boolean logic
      true_or, and_self,
      -- ULift
      ULift.down, cast_eq
    ]
  ))

  theorem _fin1_elim {P : Prop} (i : ULift (Fin2 1))
    (h : i = .up (.ofNat' 0) → P) : P :=
    match i with
    | .up (.ofNat' 0) => h rfl

  theorem _fin2_elim {P : Prop} (i : ULift (Fin2 2))
    (h1 : i = .up (.ofNat' 0) → P) (h2 : i = .up (.ofNat' 1) → P) : P :=
    match i with
    | .up (.ofNat' 0) => h1 rfl
    | .up (.ofNat' 1) => h2 rfl

  /--
  `crush_corec_eq` tries to prove equality of two `CTree`s that terminate.
  -/
  macro "crush_corec_eq" : tactic => `(tactic|(
    repeat
     (simp_corec_full
      congr
      funext i
      first
        | exact elim0_lift i
        | apply _fin2_elim i <;> intros)
  ))

  theorem par_ret_ret_eq {ε α β} {x : α} {y : β} : (ret (ε := ε) x ‖ ret y) = ret (x, y) ⊕ (zero ⊕ zero) := by
    simp only [par, parAux]
    crush_corec_eq

  theorem par_ret_ret_equiv {ε α β} {x : α} {y : β} : (ret (ε := ε) x ‖ ret y) ≈ ret (x, y) := by
    apply Euttc.eq_trans (t2 := ret (x, y) ⊕ (zero ⊕ zero))
    · rw [par_ret_ret_eq]
    · apply Euttc.eq_trans (t2 := (ret (x, y) ⊕ zero) ⊕ zero)
      · apply Euttc.eq_symm
        exact Euttc.choice_assoc
      · repeat apply Euttc.zero_right_id
        exact Euttc.eq_refl

  def parAux_def (ps : ParState ε α β) : CTree ε (α × β) :=
    match ps with
    | .lS t1 t2 =>
      match t1.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| .lS (c _fin0) t2)
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => choice (parAux <| .lS (cts _fin0) t2) (parAux <| .lS (cts _fin1) t2)
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| .parS (k {down := a}) t2)
    | .rS t1 t2 =>
      match t2.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| .rS t1 (c _fin0))
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => choice (parAux <| .rS t1 (cts _fin0)) (parAux <| .rS t1 (cts _fin1))
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| .parS t1 (k {down := a}))
    | .lrS t1 t2 => choice (parAux <| .lS t1 t2) (parAux <| .rS t1 t2)
    | .bothS t1 t2 =>
      match t1.dest, t2.dest with
      | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => ret (x, y)
      | ⟨.tau, c⟩, _ => tau (parAux <| .bothS (c _fin0) t2)
      | _, ⟨.tau, c⟩ => tau (parAux <| .bothS t1 (c _fin0))
      | ⟨.choice, cts⟩, _ =>
        choice (parAux <| .bothS (cts _fin0) t2) (parAux <| .bothS (cts _fin1) t2)
      | _, ⟨.choice, cts⟩ =>
        choice (parAux <| .bothS t1 (cts _fin0)) (parAux <| .bothS t1 (cts _fin1))
      | _, _ => zero
    | .parS t1 t2 => choice (parAux <| .bothS t1 t2) (parAux <| .lrS t1 t2)

  set_option maxHeartbeats 3200000
  lemma parAux_eq_def_left_lS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.lS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux (ParState.lS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux]
    simp_corec_base
    apply dMatchOn t1
    · intro v heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros heq
      subst heq
      exists .lS c t2
      simp_corec_full
    · intro α e k heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro a
      exists .parS (k <| ULift.down a) t2
      simp_corec_full
    · intro heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c1 c2 heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .lS c1 t2
      on_goal 2=> exists .lS c2 t2
      all_goals simp_corec_full

  lemma parAux_eq_def_left_rS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.rS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux (ParState.rS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux]
    simp_corec_base
    apply dMatchOn t2
    · intro v heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros heq
      subst heq
      exists .rS t1 c
      simp_corec_full
    · intro α e k heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro a
      exists .parS t1 (k <| ULift.down a)
      simp_corec_full
    · intro heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c1 c2 heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .rS t1 c1
      on_goal 2=> exists .rS t1 c2
      all_goals simp_corec_full

  lemma parAux_eq_def_left_lrS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.lrS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux (ParState.lrS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux]
    simp_corec_base
    apply exists_and_eq
    intro i
    apply _fin2_elim i <;> intros
    on_goal 1 => exists .lS t1 t2
    on_goal 2 => exists .rS t1 t2
    all_goals
      apply And.intro
      on_goal 2 => apply Or.inl
      all_goals simp_corec_full

  lemma parAux_eq_def_left_bothS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux (ParState.bothS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux]
    simp_corec_base
    apply exists_and_eq
    apply dMatchOn t1
    · intro v1 heq1
      apply dMatchOn t2
      · intro v2 heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS (ret v1) c
        simp_corec_full
      · intro α e k heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c1 c2 heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS (ret v1) c1
        on_goal 2 => exists .bothS (ret v1) c2
        all_goals simp_corec_full
    · intro c1 heq1
      apply dMatchOn t2
      · intro v2 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS c1 (ret v2)
        simp_corec_full
      · intro c2 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS c1 c2.tau
        simp_corec_full
      · intro α e k heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS c1 (vis e k)
        simp_corec_full
      · intro heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS c1 zero
        simp_corec_full
      · intro c21 c22 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS c1 (c21 ⊕ c22)
        simp_corec_full
    · intro α e k heq1
      apply dMatchOn t2
      · intro v2 heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c2 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS (vis e k) c2
        simp_corec_full
      · intro α e k heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c21 c22 heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS (vis e k) c21
        on_goal 2 => exists .bothS (vis e k) c22
        all_goals simp_corec_full
    · intro heq1
      apply dMatchOn t2
      · intro v2 heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c2 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS zero c2
        simp_corec_full
      · intro α e k heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro heq2 i
        subst heq1 heq2
        exact elim0_lift i
      · intro c21 c22 heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS zero c21
        on_goal 2 => exists .bothS zero c22
        all_goals simp_corec_full
    · intro c11 c12 heq1
      apply dMatchOn t2
      · intro v2 heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS c11 (ret v2)
        on_goal 2 => exists .bothS c12 (ret v2)
        all_goals simp_corec_full
      · intro c2 heq2 i
        subst heq1 heq2
        apply _fin1_elim i
        intros
        exists .bothS (c11 ⊕ c12) c2
        simp_corec_full
      · intro α e k heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS c11 (vis e k)
        on_goal 2 => exists .bothS c12 (vis e k)
        all_goals simp_corec_full
      · intro heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS c11 zero
        on_goal 2 => exists .bothS c12 zero
        all_goals simp_corec_full
      · intro c21 c22 heq2 i
        subst heq1 heq2
        apply _fin2_elim i <;> intros
        on_goal 1 => exists .bothS c11 (c21 ⊕ c22)
        on_goal 2 => exists .bothS c12 (c21 ⊕ c22)
        all_goals simp_corec_full

  lemma parAux_eq_def_left_parS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.parS t1 t2)) = ⟨a, f⟩ ∧
          PFunctor.M.dest (parAux (ParState.parS t1 t2)) = ⟨a, f'⟩ ∧
            ∀ (i : (P ε (α × β)).B a),
              (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux]
    simp_corec_base
    apply exists_and_eq
    intro i
    apply _fin2_elim i <;> intros
    on_goal 1 => exists .bothS t1 t2
    on_goal 2 => exists .lrS t1 t2
    all_goals
      apply And.intro
      on_goal 2 => apply Or.inl
      all_goals simp_corec_full

  lemma parAux_eq_def_left {ps : ParState ε α β}
    : ∃ a f f',
      PFunctor.M.dest (parAux ps) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux ps) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    match ps with
    | .lS t1 t2 => exact parAux_eq_def_left_lS
    | .rS t1 t2 => exact parAux_eq_def_left_rS
    | .lrS t1 t2 => exact parAux_eq_def_left_lrS
    | .bothS t1 t2 => exact parAux_eq_def_left_bothS
    | .parS t1 t2 => exact parAux_eq_def_left_parS

  lemma parAux_eq_def_right_lS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.lS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.lS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    simp_corec_base
    apply dMatchOn t1
    · intro v heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros heq
      subst heq
      exists .lS c t2
      simp_corec_full
    · intro α e k heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro a
      exists .parS (k <| ULift.down a) t2
      simp_corec_full
    · intro heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c1 c2 heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .lS c1 t2
      on_goal 2=> exists .lS c2 t2
      all_goals simp_corec_full

  lemma parAux_eq_def_right_rS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.rS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.rS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    simp_corec_base
    apply dMatchOn t2
    · intro v heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros heq
      subst heq
      exists .rS t1 c
      simp_corec_full
    · intro α e k heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro a
      exists .parS t1 (k <| ULift.down a)
      simp_corec_full
    · intro heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c1 c2 heq
      subst heq
      simp_ctree_mk
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .rS t1 c1
      on_goal 2=> exists .rS t1 c2
      all_goals simp_corec_full

  lemma parAux_eq_def_right_lrS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.lrS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.lrS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    simp_corec_base
    apply exists_and_eq
    intro i
    apply _fin2_elim i <;> intros
    on_goal 1 => exists .lS t1 t2
    on_goal 2 => exists .rS t1 t2
    all_goals
      apply And.intro
      on_goal 2 => apply Or.inl
      all_goals simp_corec_full

  lemma parAux_eq_def_right_bothS_ret {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS (ret (ρ := α) x) t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS (ret x) t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    apply dMatchOn t2
    · intro v2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS (ret x) c
      simp_corec_full
    · intro α e k heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c1 c2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS (ret x) c1
      on_goal 2 => exists .bothS (ret x) c2
      all_goals simp_corec_full

  lemma parAux_eq_def_right_bothS_tau {c1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS (tau c1) t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS (tau c1) t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    apply dMatchOn t2
    · intro y heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS c1 (ret y)
      simp_corec_full
    · intro c2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS c1 c2.tau
      simp_corec_full
    · intro α e k heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS c1 (vis e k)
      simp_corec_full
    · intro heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS c1 zero
      simp_corec_full
    · intro c21 c22 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS c1 (c21 ⊕ c22)
      simp_corec_full

  lemma parAux_eq_def_right_bothS_vis {ε} {α' : Type} {e : ε α'} {k : α' → CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS (vis e k) t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS (vis e k) t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    apply dMatchOn t2
    · intro y heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS (vis e k) c2
      simp_corec_full
    · intro α e k heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c21 c22 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS (vis e k) c21
      on_goal 2 => exists .bothS (vis e k) c22
      all_goals simp_corec_full

  lemma parAux_eq_def_right_bothS_zero {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS (zero (ρ := α)) t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS zero t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    apply dMatchOn t2
    · intro v2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS zero c2
      simp_corec_full
    · intro α e k heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      exact elim0_lift i
    · intro c21 c22 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS zero c21
      on_goal 2 => exists .bothS zero c22
      all_goals simp_corec_full

  lemma parAux_eq_def_right_bothS_choice {c11 c12 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS (c11 ⊕ c12) t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS (c11 ⊕ c12) t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    apply dMatchOn t2
    · intro v2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS c11 (ret v2)
      on_goal 2 => exists .bothS c12 (ret v2)
      all_goals simp_corec_full
    · intro c2 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin1_elim i
      intros
      exists .bothS (c11 ⊕ c12) c2
      simp_corec_full
    · intro α e k heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS c11 (vis e k)
      on_goal 2 => exists .bothS c12 (vis e k)
      all_goals simp_corec_full
    · intro heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS c11 zero
      on_goal 2 => exists .bothS c12 zero
      all_goals simp_corec_full
    · intro c21 c22 heq2
      subst heq2
      simp_corec_base
      apply exists_and_eq
      intro i
      apply _fin2_elim i <;> intros
      on_goal 1 => exists .bothS c11 (c21 ⊕ c22)
      on_goal 2 => exists .bothS c12 (c21 ⊕ c22)
      all_goals simp_corec_full

  lemma parAux_eq_def_right_bothS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.bothS t1 t2)) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def (ParState.bothS t1 t2)) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    apply dMatchOn t1
    · intro x heq1
      subst heq1
      exact parAux_eq_def_right_bothS_ret
    · intro c1 heq1
      subst heq1
      exact parAux_eq_def_right_bothS_tau
    · intro α e k heq1
      subst heq1
      exact parAux_eq_def_right_bothS_vis
    · intro heq1
      subst heq1
      exact parAux_eq_def_right_bothS_zero
    · intro c11 c12 heq1
      subst heq1
      exact parAux_eq_def_right_bothS_choice

  lemma parAux_eq_def_right_parS {t1 : CTree ε α} {t2 : CTree ε β}
    : ∃ a f f',
      PFunctor.M.dest (parAux (ParState.parS t1 t2)) = ⟨a, f⟩ ∧
          PFunctor.M.dest (parAux_def (ParState.parS t1 t2)) = ⟨a, f'⟩ ∧
            ∀ (i : (P ε (α × β)).B a),
              (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    simp only [parAux, parAux_def]
    simp_corec_base
    apply exists_and_eq
    intro i
    apply _fin2_elim i <;> intros
    on_goal 1 => exists .bothS t1 t2
    on_goal 2 => exists .lrS t1 t2
    all_goals
      apply And.intro
      on_goal 2 => apply Or.inl
      all_goals simp_corec_full

  lemma parAux_eq_def_right {ps : ParState ε α β}
    : ∃ a f f',
      PFunctor.M.dest (parAux ps) = ⟨a, f⟩ ∧
        PFunctor.M.dest (parAux_def ps) = ⟨a, f'⟩ ∧
          ∀ (i : (P ε (α × β)).B a),
            (fun t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) (f i) (f' i) := by
    match ps with
    | .lS t1 t2 => exact parAux_eq_def_right_lS
    | .rS t1 t2 => exact parAux_eq_def_right_rS
    | .lrS t1 t2 => exact parAux_eq_def_right_lrS
    | .bothS t1 t2 => exact parAux_eq_def_right_bothS
    | .parS t1 t2 => exact parAux_eq_def_right_parS

  theorem parAux_eq_def (ps : ParState ε α β) : parAux ps = parAux_def ps := by
    apply PFunctor.M.bisim (λ t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps)) _
    · exists ps
      apply And.intro rfl (.inr rfl)
    · intro t1 t2 ⟨ps, ⟨h1, h2⟩⟩
      cases h2 <;> (rename_i h2; subst h1 h2)
      · exact parAux_eq_def_left
      · exact parAux_eq_def_right

end CTree
