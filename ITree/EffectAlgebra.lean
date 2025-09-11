import ITree.Monad

-- ε1 usually takes the answer type or the return type
-- ε2 is usually some iterative monad m ≥ max (a + 1) e r
abbrev naturalTransformation (ε1 : Type u → Type v) (ε2 : Type max _ u → Type w) :=
  ∀ {α}, ε1 α → ε2 (ULift.{max _ u, _} α)
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

class MonadIter (m : Type max r i → Type v) where
  iter {ρ : Type r} {ι : Type i} : (ι → m (IterState ι ρ)) → ι → m (ULift ρ)

namespace ITree

inductive IterMode {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

def iter {ε : Type u → Type v} {ρ : Type r} {ι : Type i}
  (step : ι → ITree ε (IterState ι ρ)) (i : ι) : ITree ε (ULift ρ) :=
  .corec' (fun rec (s : IterMode) =>
    match s with
    | .bindS t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        match v with
        | .done r => .inl <| ret <| .up r
        | .recur l => .inr <| tau' <| rec <| .bindS (step l)
      | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS <| c 0
      | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k a
    | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
  ) (.iterS i)

instance {ε : Type a → Type e} : MonadIter (ITree ε) where
  iter := ITree.iter

def interp {ε : Type a → Type e} [Monad m] [MonadIter.{max (a + 1) e r, r, _} m]
  (handler : ∀ {α}, ε α → m (ULift.{max (a + 1) e r, _} α))
  : ITree.{a, e, r} ε ⟶ m :=
  MonadIter.iter (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => return .done v
    | ⟨.tau, c⟩ => return .recur <| c 0
    | ⟨.vis _ e, k⟩ => do
      let a ← handler e
      return .recur <| k a.down
  )

end ITree
