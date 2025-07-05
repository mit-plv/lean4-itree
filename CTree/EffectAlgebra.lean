import CTree.Monad

abbrev parametricFun (E : Type u → Type v1) (F : Type (max (max (u + 1) w1) w2) → Type v2) :=
  ∀ {α : Type u}, E α → F (ULift (ULift.{w1, _} (PLift α)))
infixr:50 " ⟹ "=> parametricFun

inductive SumE (ε1 ε2 : Type u → Type v) : Type u → Type v
  | inl {α : Type u} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type u} (e2 : ε2 α) : SumE ε1 ε2 α

instance : Add (Type u → Type v) where
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
        | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k (PLift.up a)
        | ⟨.zero, _⟩ => .inr <| zero'
        | ⟨.choice, cts⟩ => .inr <| choice' (rec <| .bindS <| cts _fin0) (rec <| .bindS <| cts _fin1)
      | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
    ) (.iterS i)

  def interp' {ε1 : Type u1 → Type v1} {ε2 : Type u2 → Type v2}
    (handler : ∀ {α : Type u1}, ε1 α → CTree ε2 (ULift (ULift.{v1, _} (PLift α))))
    {ρ : Type v3} (t : CTree ε1 ρ) : CTree ε2 ρ :=
    iter (fun t =>
      t.matchOn
      (fun v => ret <| .inr v)
      (fun t => ret <| .inl t)
      (fun e k => handler e >>= fun a => ret <| .inl <| k a.down.down.down)
      zero
      (fun c1 c2 => ret <| .inl <| c1 ⊕ c2)
    ) t
end CTree
