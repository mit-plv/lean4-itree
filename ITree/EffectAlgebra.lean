import ITree.Monad

abbrev naturalTransformation (ε1 : Type r → Type u) (ε2 : Type r → Type v) :=
  ∀ {ρ}, ε1 ρ → ε2 ρ
infixr:50 " ⟶ "=> naturalTransformation

inductive SumE (ε1 ε2 : Type u → Type v) : Type u → Type v
  | inl {α : Type u} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type u} (e2 : ε2 α) : SumE ε1 ε2 α

instance : Add (Type u → Type v) where
  add := SumE

instance {ε1 ε2 : Type u → Type v} : Coe (ε1 α) (SumE ε1 ε2 α) where
  coe e := .inl e

instance {ε1 ε2 : Type u → Type v} : Coe (ε2 α) (SumE ε1 ε2 α) where
  coe e := .inr e

instance {ε1 ε2 : Type u → Type v} : Coe (ε1 α) ((ε1 + ε2) α) where
  coe e := .inl e

instance {ε1 ε2 : Type u → Type v} : Coe (ε2 α) ((ε1 + ε2) α) where
  coe e := .inr e

inductive IterState (ι : Type u) (ρ : Type u) : Type u
  | done  (r : ρ)
  | recur (i : ι)

class MonadIter (m : Type (u + 1) → Type v) where
  iter {ρ ι} : (ι → m (IterState ι ρ)) → ι → m ρ

instance instMonadIterStateT {σ} [Monad m] [MI : MonadIter m]
  : MonadIter (StateT σ m) where
  iter step i s :=
    MonadIter.iter (fun (i, s) =>
      step i s >>= fun (i', s') =>
      match i' with
      | .done r   => pure <| .done  (r, s')
      | .recur i' => pure <| .recur (i', s')
    ) (i, s)

namespace ITree

inductive IterMode {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

def iter {ε : Type a → Type a} {ρ ι : Type (a + 1)}
  (step : ι → ITree ε (IterState ι ρ)) (i : ι) : ITree ε ρ :=
  .corec' (fun rec (s : IterMode) =>
    match s with
    | .bindS t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        match v with
        | .done r => .inl <| ret r
        | .recur l => .inr <| tau' <| rec <| .bindS (step l)
      | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS <| c 0
      | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k a
    | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
  ) (.iterS i)

instance {ε : Type a → Type a} : MonadIter (ITree ε) where
  iter := ITree.iter

def interp {ε : Type a → Type a} [Monad m] [MonadIter m] (h : ε ⟶ (m ∘ PLift))
  : ITree ε ⟶ m :=
  MonadIter.iter (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => return .done v
    | ⟨.tau, c⟩ => return .recur <| c 0
    | ⟨.vis _ e, k⟩ => do
      let a ← h e
      return .recur <| k a.down
  )

end ITree
