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

  macro "simp_corec_full" : tactic => `(tactic|(
    simp_all only [
      -- `PFunctor.M.corec` related
      corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
      -- Other `PFunctor` things
      PFunctor.map, PFunctor.map_eq, PFunctor.M.dest_mk,
      -- Get rid of `Sum.bind` in `PFunctor.M.corec'`
      Bind.bind, Sum.bind,
      -- `CTree` constructors
      mk, ret, ret', vis, vis', tau, tau', zero, zero', choice, choice',
      -- General function things
      Function.comp_apply, Function.id_comp, id_eq,
      -- `Vector3` related
      Fin2.ofNat', _fin2Const, Vector3.cons_fz, Vector3.cons_fs,
      -- `Nat` related
      Nat.reduceAdd
    ]
  ))

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

  namespace TraceEq
    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · apply Refine.coind (λ p1 p2 t1 t2 => ∃ t, t1 = (ret x) ‖→ t ∧ t2 = t) _ ⊤ ⊤
        -- · repeat apply And.intro rfl
        · exists t
        · intro p1 p2 _ t h
          obtain ⟨_, ht1, ht2⟩ := h
          -- subst hp1
          -- subst hp2
          subst ht1
          subst ht2
          apply dMatchOn t
          · intro v heq
            subst heq
            simp only [parR]
            sorry
            -- simp only [parR, par, parBoth_ret_ret, parLeft_ret_ret, parRight_ret_ret,
            --   Functor.map, map_choice, map_zero, map_ret]
            -- apply RefineF.choice_idemp
            -- · apply RefineF.choice_idemp
            --   <;> exact RefineF.zero
            -- · exact RefineF.ret rfl
          · intro c heq
            subst heq
            -- simp only [parR, par, parBoth_ret_tau]
            sorry
          · sorry
          · sorry
          · sorry
      · sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end TraceEq

end CTree
