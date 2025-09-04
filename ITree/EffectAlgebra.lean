import ITree.Monad

abbrev parametricFun (E : Type u → Type v1) (F : Type u → Type v2) :=
  ∀ {α : Type u}, E α → F α
infixr:50 " ⟹ "=> parametricFun

inductive SumE (ε1 ε2 : Type u → Type v) : Type u → Type v
  | inl {α : Type u} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type u} (e2 : ε2 α) : SumE ε1 ε2 α

instance : Add (Type u → Type v) where
  add := SumE

namespace ITree

inductive iterState {ε ρ ι}
| iterS (i : ι)
| bindS (t : ITree ε (ι ⊕ ρ))

def iter {ε ρ ι} (step : ι → ITree ε (ι ⊕ ρ)) (i : ι) : ITree ε ρ :=
  .corec' (fun rec (s : iterState) =>
    match s with
    | .bindS t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        match v with
        | .inl l => .inr <| tau' <| rec <| .bindS (step l)
        | .inr r => .inl <| ret r
      | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS <| c 0
      | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k a
    | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
  ) (.iterS i)

def interp {ε1 : Type u1 → Type v1} {ε2 : Type u2 → Type v2}
  (handler : ε1 ⟹ ITree ε2) {ρ : Type v3} (t : ITree ε1 ρ) : ITree ε2 ρ :=
  iter (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => ret <| .inr v
    | ⟨.tau, c⟩ => ret <| .inl (c 0)
    | ⟨.vis _ e, k⟩ => (handler e).bind <| fun a => ret <| .inl <| k a -- using >>= messes up universes
  ) t

end ITree
