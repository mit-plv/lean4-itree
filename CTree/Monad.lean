import CTree.Basic

namespace CTree
  /- Functor Instance -/
  def map (f : α → β) (t : CTree ε α) : CTree ε β :=
    .corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| ret <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k)
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
  theorem map_ret {ε : Type u1 → Type v1} : map (ε := ε) f (ret v) = ret (f v) := by
    conv => lhs; simp only [map]
    rw [unfold_corec', dest_ret]

  theorem map_tau {ε : Type u1 → Type v1} {c : CTree ε ρ} : map f (tau c) = tau (map f c) := by
    conv => lhs; simp only [map]
    rw [unfold_corec', dest_tau]
    simp only [tau, tau']
    congr; funext i
    match i with
    | (.up (.ofNat' 0)) => rfl

  theorem map_vis {ε : Type u1 → Type v1} {α : Type u1} {e : ε α} {k : α → CTree ε ρ} {f : ρ → σ}
    : map f (vis e k) = vis e (λ x => map f <| k x) := by
    conv => lhs; simp only [map]
    rw [unfold_corec', dest_vis]
    simp only [vis, vis']
    congr

  theorem map_zero {ε} {f : α → β} : map (ε := ε) f zero = zero := by
    conv => lhs; simp only [map]
    rw [unfold_corec', dest_zero]

theorem map_choice {f : α → β} : map f (choice c1 c2) = choice (map f c1) (map f c2) := by
    conv => lhs; simp only [map]
    rw [unfold_corec', dest_choice]
    simp only [choice, choice']
    congr; funext i
    match i with
    | .up (.ofNat' 0) => rfl
    | .up (.ofNat' 1) => rfl

  /- Monad Instance -/
  def bind {σ} (t : CTree ε ρ) (f : ρ → CTree ε σ) : CTree ε σ :=
    .corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k)
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
    conv => lhs; simp only [bind]
    rw [unfold_corec', dest_ret]

  theorem bind_tau : bind (tau c) f = tau (bind c f) := by
    conv => lhs; simp only [bind]
    rw [unfold_corec', dest_tau]
    simp only [tau, tau']
    congr; funext i
    match i with
    | .up (.ofNat' 0) => rfl

  theorem bind_vis : bind (vis e k) f = vis e λ x => bind (k x) f := by
    conv => lhs; simp only [bind]
    rw [unfold_corec', dest_vis]
    simp only [vis, vis']
    congr

  theorem bind_zero : bind zero f = zero := by
    conv => lhs; simp only [bind]
    rw [unfold_corec', dest_zero]

  theorem bind_choice : bind (choice c1 c2) f = choice (bind c1 f) (bind c2 f) := by
    conv => lhs; simp only [bind]
    rw [unfold_corec', dest_choice]
    simp only [choice, choice']
    congr; funext i
    match i with
    | .up (.ofNat' 0) => rfl
    | .up (.ofNat' 1) => rfl

  /- Functor Laws -/

  /--
    `ctree_eq t` tries to prove the equivalence of two `CTree`s transformed by `map` and `bind`.

    `t` is the tree to be reverted
  -/
  macro "ctree_eq" t:ident : tactic => `(tactic|(
    rw [← eq_eq]
    revert $t
    pcofix cih
    intro t
    pfold
    apply dMatchOn t <;> (intros; rename_i h; subst h)
    · repeat rw [map_ret]
      repeat rw [bind_ret]
      constructor
    · repeat rw [map_tau]
      repeat rw [bind_tau]
      constructor; pleft; apply cih
    · repeat rw [map_vis]
      repeat rw [bind_vis]
      constructor; intros; pleft; apply cih
    · repeat rw [map_zero]
      repeat rw [bind_zero]
      constructor
    · repeat rw [map_choice]
      repeat rw [bind_choice]
      constructor <;> (pleft; apply cih)
  ))

  theorem id_map (t : CTree ε ρ) : map id t = t := by ctree_eq t

  theorem comp_map (g : α → β) (h : β → γ) (t : CTree ε α) : map (h ∘ g) t = map h (map g t) := by
    ctree_eq t

  instance : LawfulFunctor (CTree ε) where
    map_const := by simp only [Functor.mapConst, Functor.map, implies_true]
    id_map := id_map
    comp_map := comp_map

  /- Monad Laws -/

  theorem map_const_left : map (Function.const α v) t = bind t λ _ => ret v := by
    ctree_eq t

  theorem map_const_right : map (Function.const α id v) t = t := by
    rw [Function.const]
    apply id_map

  /--
    `ctree_eq_map_const R t` tries to prove the equivalence of two `CTree`s transformed by `seq` and `map` with `Function.const`.

    `x` and `y` are the trees to be reverted
  -/
  macro "ctree_eq_map_const" x:ident y:ident : tactic => `(tactic|(
    simp only [SeqRight.seqRight, SeqLeft.seqLeft, Seq.seq, Functor.map]
    rw [← eq_eq]
    revert $x $y
    pcofix cih
    intro x y
    pfold
    apply dMatchOn x <;> (intros; rename_i h; subst h)
    · repeat rw [map_ret]
      repeat rw [bind_ret]
      repeat rw [map_const_left]
      repeat rw [map_const_right]
      apply eq_refl
      intros _ _ h
      pright
      pinit at h
      pmon <;> try assumption
      ptop
    · repeat rw [map_tau]
      repeat rw [bind_tau]
      constructor; pleft; apply cih
    · repeat rw [map_vis]
      repeat rw [bind_vis]
      constructor; intros; pleft; apply cih
    · repeat rw [map_zero]
      repeat rw [bind_zero]
      constructor
    · repeat rw [map_choice]
      repeat rw [bind_choice]
      constructor <;> (pleft; apply cih)
  ))

  theorem seqLeft_eq (x : CTree ε α) (y : CTree ε β) : x <* y = Function.const β <$> x <*> y := by
    ctree_eq_map_const x y

  theorem seqRight_eq (x : CTree ε α) (y : CTree ε β) : x *> y = Function.const α id <$> x <*> y := by
    ctree_eq_map_const x y

  theorem pure_seq (g : α → β) (x : CTree ε α) : pure g <*> x = g <$> x := by
    simp only [Seq.seq, pure, bind_ret]

  theorem bind_pure_comp (f : α → β) (x : CTree ε α) : bind x (pure ∘ f) = map f x := by
    ctree_eq x

  theorem pure_bind (x : α) (f : α → CTree ε β) : bind (pure x) f = f x := by
    simp only [pure, bind_ret]

  theorem bind_assoc (x : CTree ε α) (f : α → CTree ε β) (g : β → CTree ε γ)
    : bind (bind x f) g = bind x λ x => bind (f x) g := by
    rw [← eq_eq]
    revert x f g
    pcofix cih
    intro x f g
    apply dMatchOn x <;> (intros; rename_i h; subst h)
    · repeat rw [bind_ret]
      rename_i a; pfold
      apply eq_refl
      intros _ _ h
      pinit at h
      pright
      pmon <;> try assumption
      ptop
    · repeat rw [bind_tau]
      pfold; constructor; pleft; apply cih
    · repeat rw [bind_vis]
      pfold; constructor; intros; pleft; apply cih
    · repeat rw [bind_zero]
      pfold; constructor
    · repeat rw [bind_choice]
      pfold; constructor <;> (pleft; apply cih)

  instance : LawfulMonad (CTree ε) where
    seqLeft_eq := seqLeft_eq
    seqRight_eq := seqRight_eq
    pure_seq := pure_seq
    bind_pure_comp := bind_pure_comp
    bind_map := bind_map
    pure_bind := pure_bind
    bind_assoc := bind_assoc
end CTree
