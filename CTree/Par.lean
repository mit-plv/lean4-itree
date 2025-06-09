import CTree.Basic
import CTree.Monad
import CTree.Euttc

namespace CTree
  /- Paralle Opeartor -/

  -- State for the parallel operator corecursion
  inductive ParState (ε : Type → Type) (α β : Type)
    | left (t1 : CTree ε α) (t2 : CTree ε β)   -- ◁ operator
    | right (t1 : CTree ε α) (t2 : CTree ε β)  -- ▷ operator
    | both (t1 : CTree ε α) (t2 : CTree ε β)   -- ⊲⊳ operator

  /--
  Extended corecursion that can handle mixed depths
  The key insight: allow the function to return either:
  - A final result `(P.M)`
  - One layer of constructor `(P X)`
  - Two layers of constructor with a mix `(P (P (P X ⊕ X)))`
  - A mix where left and right have different depths `(P X ⊕ X)`
  -/
  def corecAsym {P : PFunctor.{u}} {α : Type u}
    (F : ∀ {X : Type u}, (α → X) → α → P.M ⊕ P X ⊕ P (P (P X ⊕ X))) (x : α) : P.M :=
    .corec (λ (state : P.M ⊕ P α ⊕ P (P (P α ⊕ α)) ⊕ P (P α ⊕ α) ⊕ α) =>
      match state with
      | .inl result =>
        -- Final result, just unfold it
        P.map .inl result.dest
      | .inr (.inl px) =>
        -- One layer: P X -> continue with X
        ⟨px.1, λ i => .inr <| .inr <| .inr <| .inr <| px.2 i⟩
      | .inr (.inr (.inl ppx)) =>
        -- Two layers: P (P (P X ⊕ X)) -> continue with P (P X ⊕ X)
        ⟨ppx.1, λ i => .inr <| .inr <| .inr <| .inl <| ppx.2 i⟩
      | .inr (.inr (.inr (.inl pmix))) =>
        -- Mixed: P (P X ⊕ X) -> handle the sum
        ⟨pmix.1, λ i =>
          match pmix.2 i with
          | .inl px => .inr <| .inl px  -- P X case
          | .inr x => .inr <| .inr <| .inr <| .inr x  -- X case
        ⟩
      | .inr (.inr (.inr (.inr y))) =>
        -- Initial state, apply the function
        match F id y with
        | .inl result =>
          P.map .inl result.dest
        | .inr (.inl px) =>
          ⟨px.1, λ i => .inr <| .inr <| .inr <| .inr <| px.2 i⟩
        | .inr (.inr pmix) =>
          ⟨pmix.1, λ i => .inr <| .inr <| .inr <| .inl <| pmix.2 i⟩
    ) (.inr <| .inr <| .inr <| .inr x)

  def parAux (ps : ParState ε α β) : CTree ε (α × β) :=
    corecAsym (λ rec state =>
      match state with
      | .left t1 t2 =>
        match t1.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ => .inr <| .inl <| tau' <| rec <| .left (c _fin0) t2
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ => .inr <| .inl <| choice' (rec <| .left (cts _fin0) t2) (rec <| .left (cts _fin1) t2)
        | ⟨.vis _ e, k⟩ =>
          .inr <| .inr <| vis' e λ a =>
            let k := k (.up a)
            choice' (.inl <| choice' (rec <| .left k t2) (rec <| .right k t2)) (.inr <| rec <| .both k t2)
      | .right t1 t2 =>
        match t2.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ => .inr <| .inl <| tau' <| rec <| .right t1 (c _fin0)
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ => .inr <| .inl <| choice' (rec <| .right t1 (cts _fin0)) (rec <| .right t1 (cts _fin1))
        | ⟨.vis _ e, k⟩ =>
          .inr <| .inr <| vis' e λ a =>
            let k := k (.up a)
            choice' (.inl <| choice' (rec <| .left t1 k) (rec <| .right t1 k)) (.inr <| rec <| .both t1 k)
      | .both t1 t2 =>
        match t1.dest, t2.dest with
        | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => .inl <| ret (x, y)
        /-
          Note about the choice cases. Our implementation can express infinite non-determinism,
          which the original Bahr and Hutton formalization cannot. This means that this `both` case
          is always biased towards the left when destructing choices. However, if the left side contains
          infinite non-determinism, it does not return. So this should still respect the semantics of the
          parallel operator. We can maybe get around this by having a case where both sides are choices,
          but the massive 4-way choice that results from it might not be worth it.
        -/
        | ⟨.choice, cts1⟩, _ => .inr <| .inl <| choice' (rec <| .both (cts1 _fin0) t2) (rec <| .both (cts1 _fin1) t2)
        | _, ⟨.choice, cts2⟩ => .inr <| .inl <| choice' (rec <| .both t1 (cts2 _fin0)) (rec <| .both t1 (cts2 _fin1))
        | ⟨.tau, c1⟩, ⟨.tau, c2⟩ => .inr <| .inl <| tau' <| rec <| .both (c1 _fin0) (c2 _fin0)
        | ⟨.tau, c1⟩, _ => .inr <| .inl <| tau' <| rec <| .both (c1 _fin0) t2
        | _, ⟨.tau, c2⟩ => .inr <| .inl <| tau' <| rec <| .both t1 (c2 _fin0)
        | _, _ => .inl zero
    ) ps

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    choice
      (choice (parAux <| .left t1 t2) (parAux <| .right t1 t2))
      (parAux <| .both t1 t2)
  infixr:60 " || " => par

  theorem parBoth_ret_ret : (parAux (.both (ret (ε := ε) x) (ret y))) = ret (x, y) := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = parAux (.both (ret x) (ret y)) ∧ t2 = ret (x, y))
    · intro t1 t2 h
      obtain ⟨ht1, ht2⟩ := h
      subst ht1
      subst ht2
      simp only [parAux, corecAsym, PFunctor.M.corec_def]
      apply exists_and_eq
      intro i
      simp only [P, children, zero, mk, zero', tau', id_eq, choice', vis', ret, ret',
        PFunctor.M.dest_mk, PFunctor.map_map, PFunctor.M.head_mk, PFunctor.fst_map] at i
      apply elim0_lift i
    · exact And.intro rfl rfl

  theorem parLeft_ret_ret : (parAux (.left (ret (ε := ε) x) (ret y))) = zero := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = parAux (.left (ret x) (ret y)) ∧ t2 = zero)
    · intro t1 t2 h
      obtain ⟨ht1, ht2⟩ := h
      subst ht1
      subst ht2
      simp only [parAux, corecAsym, PFunctor.M.corec_def]
      apply exists_and_eq
      intro i
      simp only [P, children, zero, mk, zero', tau', id_eq, choice', vis', ret, ret',
        PFunctor.M.dest_mk, PFunctor.map_map, PFunctor.M.head_mk, PFunctor.fst_map] at i
      apply elim0_lift i
    · exact And.intro rfl rfl

  theorem parRight_ret_ret : (parAux (.right (ret (ε := ε) x) (ret y))) = zero := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = parAux (.right (ret x) (ret y)) ∧ t2 = zero)
    · intro t1 t2 h
      obtain ⟨ht1, ht2⟩ := h
      subst ht1
      subst ht2
      simp only [parAux, corecAsym, PFunctor.M.corec_def]
      apply exists_and_eq
      intro i
      simp only [P, children, zero, mk, zero', tau', id_eq, choice', vis', ret, ret',
        PFunctor.M.dest_mk, PFunctor.map_map, PFunctor.M.head_mk, PFunctor.fst_map] at i
      apply elim0_lift i
    · exact And.intro rfl rfl

  theorem parBoth_ret_tau {t : CTree ε ρ} : parAux (.both (ret x) t.tau) = (parAux <| .both (ret x) t).tau := by
    -- apply PFunctor.M.bisim (λ t1 t2 => t1 = parAux (.both (ret x) t.tau))
    sorry

  theorem par_ret_ret : (ret (ε := ε) x || ret y) ≈ ret (x, y) := by
    simp only [par]
    rw [parBoth_ret_ret, parLeft_ret_ret, parRight_ret_ret]
    apply Euttc.eq_trans (t2 := zero ⊕ (zero ⊕ ret (x, y)))
    · exact Euttc.choice_assoc
    · apply Euttc.eq_trans (t2 := zero ⊕ ret (x, y))
      <;> exact .zero_left_id

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 || t2)
  infixr:60 " ||→ " => parR

  namespace TraceEq
    theorem parR_ret : ((ret x) ||→ t) ≈ t := by
      apply And.intro
      · apply Refine.coind (λ p1 p2 t1 t2 => ∃ t, t1 = (ret x) ||→ t ∧ t2 = t) _ ⊤ ⊤
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
            simp only [parR, par, parBoth_ret_ret, parLeft_ret_ret, parRight_ret_ret,
              Functor.map, map_choice, map_zero, map_ret]
            apply RefineF.choice_idemp
            · apply RefineF.choice_idemp
              <;> exact RefineF.zero
            · exact RefineF.ret rfl
          · intro c heq
            subst heq
            simp only [parR, par, parBoth_ret_tau]
            sorry
          · sorry
          · sorry
          · sorry
      · sorry

    theorem parR_map : ((map f t1) ||→ t2) ≈ (t1 ||→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ||→ t2) ||→ t3) ≈ (t1 ||→ (t2 ||→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ||→ t2) ||→ t3) ≈ ((t2 ||→ t1) ||→ t3) := by
      sorry
  end TraceEq

end CTree
