import ITree.Monad

abbrev naturalTransformation (ε1 : Type u → Type v1) (ε2 : Type u → Type v2) :=
  ∀ {α : Type u}, ε1 α → ε2 α
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

inductive IterState (ι : Type u) (ρ : Type v)
  | done  (r : ρ)
  | recur (i : ι)

class MonadIter (m : Type u -> Type v) where
  iter : {ρ ι : Type u} → (ι -> m (IterState ι ρ)) -> ι -> m ρ

namespace ITree

inductive IterMode {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

def iter {ε ρ ι} (step : ι → ITree ε (IterState ι ρ)) (i : ι) : ITree ε ρ :=
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

instance {ε : Type u → Type v} : MonadIter (ITree ε) where
  iter := ITree.iter

def interp {ε m : Type u → Type v} {ρ : Type u} [MonadIter m]
  (handler : ε ⟶ m) (t : ITree ε ρ) : m ρ :=
  MonadIter.iter (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => ret <| .done v
    | ⟨.tau, c⟩ => ret <| .recur (c 0)
    | ⟨.vis _ e, k⟩ => (handler e).bind <| fun a => ret <| .recur <| k a -- using >>= messes up universes
  ) t

end ITree
