import CTree.Monad

abbrev parametricFun (E : Type u → Type v1) (F : Type u → Type v2) :=
  ∀ {α : Type u}, E α → F α
infixr:50 " ⟹ "=> parametricFun

inductive SumE (ε1 ε2 : Type → Type) : Type → Type
  | inl {α : Type} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type} (e2 : ε2 α) : SumE ε1 ε2 α

instance : Add (Type → Type) where
  add := SumE

namespace CTree

  inductive iterState {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : CTree ε (ι ⊕ ρ))

  def iter {ε ρ ι} (step : ι → CTree ε (ι ⊕ ρ)) (i : ι) : CTree ε ρ :=
    .corec' (fun rec (s : iterState) =>
      match s with
      | .bindS t =>
        match t.dest with
        | ⟨.ret v, _⟩ =>
          match v with
          | .inl l => .inr <| tau' <| rec <| .bindS (step l)
          | .inr r => .inl <| ret r
        | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS <| c _fin0
        | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k (ULift.up a)
        | ⟨.zero, _⟩ => .inr <| zero'
        | ⟨.choice, cts⟩ => .inr <| choice' (rec <| .bindS <| cts _fin0) (rec <| .bindS <| cts _fin1)
      | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
    ) (.iterS i)

  inductive interpState {ε1 ε2 ρ}
  | iterS (i : CTree ε1 ρ)
  | bindS (t : CTree ε2 α) (tk : α → CTree ε1 ρ)

  /--
    Interpret `CTree`s of one effect type into a `CTree` with a different effect type.
  -/
  def interp {ε1 ε2 ρ} (handler : ε1 ⟹ CTree ε2) (t : CTree ε1 ρ) : CTree ε2 ρ :=
    .corec' (fun rec (s : interpState) =>
      match s with
      | .bindS t tk =>
        match t.dest with
        | ⟨.ret v, _⟩ => .inr <| tau' <| rec <| .iterS (tk v)
        | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS (c _fin0) tk
        | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS (k (ULift.up a)) tk
        | ⟨.zero, _⟩ => .inr <| zero'
        | ⟨.choice, cts⟩ => .inr <| choice' (rec <| .bindS (cts _fin0) tk) (rec <| .bindS (cts _fin1) tk)
      | .iterS t =>
        match t.dest with
        | ⟨.ret v, _⟩ => .inl <| ret v
        | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .iterS (c _fin0)
        | ⟨.vis _ e, k⟩ => .inr <| tau' <| rec <| .bindS (handler e) (fun a => k <| .up a)
        | ⟨.zero, _⟩ => .inr <| zero'
        | ⟨.choice, cts⟩ => .inr <| choice' (rec <| .iterS (cts _fin0)) (rec <| .iterS (cts _fin1))
    ) (.iterS t)

end CTree
