import CTree.Basic

namespace CTree
  /- Functor Instance -/
  def map (f : α → β) (t : CTree ε α) : CTree ε β :=
    corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| ret <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k ∘ .up)
      | ⟨.zero, _⟩ =>
        .inl zero
      | ⟨.choice, cts⟩ =>
        let t1 := rec <| cts _fin0
        let t2 := rec <| cts _fin1
        .inr <| choice' t1 t2
    ) t

  instance : Functor (CTree ε) where
    map := map

  /- Basic map lemmas -/
  theorem map_ret {ε : Type → Type} : map (ε := ε) f (ret v) = ret (f v) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    exact _elim0_eq_all _

  theorem map_tau {ε : Type → Type} {c : CTree ε ρ} : map f (tau c) = tau (map f c) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', tau,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin1Const, Fin2.ofNat', Function.comp_apply, PFunctor.M.corec_def]
      rfl

  theorem map_vis {ε : Type → Type} {α : Type} {e : ε α} {k : α → CTree ε ρ} {f : ρ → σ}
    : map f (vis e k) = vis e (λ x => map f <| k x) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', vis,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    simp only [Function.comp_apply, PFunctor.M.corec_def]

  theorem map_zero {ε} {f : α → β} : map (ε := ε) f zero = zero := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    exact _elim0_eq_all _

  theorem map_choice {f : α → β} : map f (choice c1 c2) = choice (map f c1) (map f c2) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', choice,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin2Const, Nat.reduceAdd, Fin2.ofNat', Function.comp_apply, Vector3.cons_fz,
        PFunctor.M.corec_def]
      rfl
    | .up (.ofNat' 1) =>
      simp only [_fin2Const, Nat.reduceAdd, Fin2.ofNat', Function.comp_apply, Vector3.cons_fz,
        PFunctor.M.corec_def]
      rfl

  theorem map_ret_eq (h : f <$> t1 = ret y) : ∃ x, f x = y ∧ t1 = ret x := by
    apply dMatchOn t1
    · intro x heq
      simp only [heq, Functor.map, map_ret] at h
      exists x
      exact And.intro (ret_inj h) heq
    on_goal 1 => intro _ heq
    on_goal 2 => intro _ _ _ heq
    on_goal 3 => intro heq
    on_goal 4 => intro _ _ heq
    all_goals
     (rw [heq] at h
      simp only [heq, Functor.map, map_tau, map_vis, map_zero, map_choice] at h
      ctree_elim h)

  /- Monad Instance -/
  def bind {σ} (t : CTree ε ρ) (f : ρ → CTree ε σ) : CTree ε σ :=
    corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k ∘ .up)
      | ⟨.zero, _⟩ =>
        .inl zero
      | ⟨.choice, cts⟩ =>
        let t1 := rec <| cts _fin0
        let t2 := rec <| cts _fin1
        .inr <| choice' t1 t2
    ) t

  instance : Monad (CTree ε) where
    pure := ret
    bind := bind

  theorem bind_map (f : CTree ε (α → β)) (x : CTree ε α) : (f >>= λ f => map f x) = f <*> x := by
    simp only [Bind.bind, Seq.seq, Functor.map]

  /- Bind monad lemmas -/
  theorem bind_ret : bind (ret v) f = f v := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', ret, ret',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_map]
    rw [PFunctor.M.map_dest]
    conv =>
      rhs
      rw [←PFunctor.M.mk_dest (x := f v)]
    match hm : PFunctor.M.dest (f v) with
    | ⟨fst, snd⟩ =>
      congr
      apply corec_inl_eq_id
      simp only [implies_true]

  theorem bind_tau : bind (tau c) f = tau (bind c f) := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      tau, PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [Function.comp_apply, PFunctor.M.corec_def]
      rfl

  theorem bind_vis : bind (vis e k) f = vis e λ x => bind (k x) f := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      vis, PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    funext i
    simp only [Function.comp_apply, PFunctor.M.corec_def]
    rfl

  theorem bind_zero : bind zero f = zero := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    exact _elim0_eq_all _

  theorem bind_choice : bind (choice c1 c2) f = choice (bind c1 f) (bind c2 f) := by
    simp [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def, PFunctor.map, Bind.bind, Sum.bind]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin0, _fin2Const, Nat.reduceAdd, Function.comp_apply, PFunctor.M.corec_def]
      rfl
    | .up (.ofNat' 1) =>
      simp only [_fin0, _fin2Const, Nat.reduceAdd, Function.comp_apply, PFunctor.M.corec_def]
      rfl

  /- Functor Laws -/

  /--
    `ctree_eq R t` tries to prove the equivalence of two `CTree`s transformed by `map` and `bind`.

    `R` should be of the form `λ t1 t2 => ∃ t, t1 = f t ∧ t2 = g t` where `f` and `g` are some function from `CTree` to `CTree` potentially involving `map` and `bind`.

    `t` is the initial value passed to the existential in `R`.
  -/
  macro "ctree_eq" " (" R:term ") " t:term : tactic => `(tactic|(
    apply PFunctor.M.bisim $R _
    · exists $t
    · intro x y h
      obtain ⟨t, h⟩ := h
      rw [h.left, h.right]
      apply dMatchOn t
      · intro v h
        simp only [h, map_ret, bind_ret, dest_ret, id]
        apply exists_and_eq
        intro i
        exact elim0_lift i
      · intro c h
        simp only [h, map_tau, bind_tau, dest_tau]
        apply exists_and_eq
        intro i
        exists c
        match i with
        | .up (.ofNat' 0) =>
          apply And.intro <;> simp only [_fin1Const, Fin2.ofNat']
      · intro α e k h
        simp only [h, map_vis, bind_vis, dest_vis]
        apply exists_and_eq
        intro i
        exists (k ∘ ULift.down) i
      · intro h
        simp only [h, map_zero, bind_zero, dest_zero]
        apply exists_and_eq
        intro i
        exact elim0_lift i
      · intro c1 c2 h
        simp only [h, map_choice, bind_choice, dest_choice]
        apply exists_and_eq
        intro i
        match i with
        | .up (.ofNat' 0) =>
          exists c1
        | .up (.ofNat' 1) =>
          exists c2
  ))

  theorem id_map (t : CTree ε ρ) : map id t = t := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map id t ∧ t2 = t) t

  theorem comp_map (g : α → β) (h : β → γ) (t : CTree ε α) : map (h ∘ g) t = map h (map g t) := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (h ∘ g) t ∧ t2 = map h (map g t)) t

  instance : LawfulFunctor (CTree ε) where
    map_const := by simp only [Functor.mapConst, Functor.map, implies_true]
    id_map := id_map
    comp_map := comp_map

  /- Monad Laws -/

  theorem map_const_left : map (Function.const α v) t = bind t λ _ => ret v := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (Function.const α v) t ∧ t2 = t.bind λ _ => ret v) t

  theorem map_const_right : map (Function.const α id v) t = t := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (Function.const α id v) t ∧ t2 = t) t

  /--
    `ctree_eq_map_const R t` tries to prove the equivalence of two `CTree`s transformed by `seq` and `map` with `Function.const`.

    `R` should be of the form `λ t1 t2 => t1 = t2 ∨ ∃ x y, t1 = f x y ∧ t2 = g x y`.

    `x` and `y` are the initial values passed to the existential in `R`.
  -/
  macro "ctree_eq_map_const" " (" R:term ") " x:term ", " y:term : tactic => `(tactic|(
    apply PFunctor.M.bisim $R _
    · apply Or.inr
      exists $x, $y
    · intro x y h
      match h with
      | .inl h =>
        match hm : x.dest with
        | ⟨a, f⟩ =>
          exists a, f, f
          apply And.intro rfl
          apply And.intro _ λ _ => .inl rfl
          rw [←hm, h]
      | .inr ⟨x, y, h⟩ =>
        rw [h.left, h.right]
        simp only [SeqLeft.seqLeft, SeqRight.seqRight, Seq.seq, Functor.map]
        apply dMatchOn x
        · intro v h
          simp only [h, bind_ret, map_ret, map_const_left, map_const_right]
          apply exists_and_eq
          intro i
          exact Or.inl rfl
        · intro c h
          simp only [h, bind_tau, map_tau]
          simp only [tau, mk, tau', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c, y
        · intro _ e k h
          simp only [h, bind_vis, map_vis]
          simp only [vis, mk, vis']
          apply exists_and_eq
          intro i
          apply Or.inr
          exists k i.down, y
        · intro h
          simp only [h, bind_zero, map_zero]
          simp only [zero, mk, zero', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          exact elim0_lift i
        · intro c1 c2 h
          simp only [h, bind_choice, map_choice]
          simp only [choice, mk, choice', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c1, y
          | .up (.ofNat' 1) =>
            exists c2, y
  ))

  theorem seqLeft_eq (x : CTree ε α) (y : CTree ε β) : x <* y = Function.const β <$> x <*> y := by
    ctree_eq_map_const (λ t1 t2 => (t1 = t2) ∨ ∃ (x : CTree ε α) (y : CTree ε β), (t1 = x <* y ∧ t2 = (Function.const β <$> x <*> y))) x, y

  theorem seqRight_eq (x : CTree ε α) (y : CTree ε β) : x *> y = Function.const α id <$> x <*> y := by
    ctree_eq_map_const (λ t1 t2 => t1 = t2 ∨ ∃ (x : CTree ε α) (y : CTree ε β), t1 = x *> y ∧ t2 = Function.const α id <$> x <*> y) x, y

  theorem pure_seq (g : α → β) (x : CTree ε α) : pure g <*> x = g <$> x := by
    simp only [Seq.seq, pure, bind_ret]

  theorem bind_pure_comp (f : α → β) (x : CTree ε α) : bind x (pure ∘ f) = map f x := by
    ctree_eq (λ t1 t2 => ∃ x, t1 = bind x (pure ∘ f) ∧ t2 = map f x) x

  theorem pure_bind (x : α) (f : α → CTree ε β) : bind (pure x) f = f x := by
    simp only [pure, bind_ret]

  theorem bind_assoc (x : CTree ε α) (f : α → CTree ε β) (g : β → CTree ε γ)
    : bind (bind x f) g = bind x λ x => bind (f x) g := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = t2 ∨ ∃ x, t1 = bind (bind x f) g ∧ t2 = bind x λ x => bind (f x) g) _
    · apply Or.inr
      exists x
    · intro x y h
      match h with
      | .inl h =>
        match hm : PFunctor.M.dest x with
        | ⟨a, f⟩ =>
          exists a, f, f
          apply And.intro rfl
          apply And.intro _ λ _ => Or.inl rfl
          rw [←hm, h]
      | .inr ⟨x, h⟩ =>
        rw [h.left, h.right]
        apply dMatchOn x
        · intro v h
          simp only [h, bind_ret, map_ret]
          match hm : PFunctor.M.dest (bind (f v) g) with
          | ⟨a, f⟩ =>
            exists a, f, f
            repeat apply And.intro rfl
            intro
            exact Or.inl rfl
        · intro c h
          simp only [h, bind_tau, map_tau]
          simp only [tau, mk, tau']
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c
        · intro _ e k h
          simp only [h, bind_vis, map_vis]
          simp only [vis, mk, vis']
          apply exists_and_eq
          intro i
          apply Or.inr
          exists k i.down
        · intro h
          simp only [h, bind_zero, map_zero]
          simp only [zero, mk, zero']
          apply exists_and_eq
          intro i
          exact elim0_lift i
        · intro c1 c2 h
          simp only [h, bind_choice, map_choice]
          simp only [choice, mk, choice']
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c1
          | .up (.ofNat' 1) =>
            exists c2

  instance : LawfulMonad (CTree ε) where
    seqLeft_eq := seqLeft_eq
    seqRight_eq := seqRight_eq
    pure_seq := pure_seq
    bind_pure_comp := bind_pure_comp
    bind_map := bind_map
    pure_bind := pure_bind
    bind_assoc := bind_assoc
end CTree
