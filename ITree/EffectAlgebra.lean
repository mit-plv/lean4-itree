import ITree.Monad

abbrev naturalTransformation (ε1 : Type u → Type v1) (ε2 : Type (max u v) → Type v2) :=
  ∀ {α : Type u}, ε1 α → ε2 (ULift α)
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

class MonadIter (m : Type max i r → Type v) where
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

instance {ε : Type u → Type v} : MonadIter (ITree ε) where
  iter := ITree.iter

def interp {ε : Type u → Type v}
  [Monad m] [MonadIter.{r, max (max (max (u + 1) r) v) u, _} m]
  (h : ∀ {α}, ε α → m (ULift.{max (max (u + 1) r) v, u} α))
  : ∀ {ρ : Type r}, ITree ε ρ → m (ULift.{max (max (u + 1) r) v, r} ρ) :=
  fun t =>
  MonadIter.iter.{r, max (max (max (u + 1) r) v) u, _} (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => pure <| .done v
    | ⟨.tau, c⟩ => pure <| .recur <| c 0
    | ⟨.vis α e, k⟩ =>
      Functor.map (fun a : ULift.{max (max (u + 1) r) v, _} α => .recur <| k a.down) (h e)
  ) t

end ITree
