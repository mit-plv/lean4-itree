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

  /--
    Interpret `CTree`s of one effect type into a `CTree` with a different effect type.
  -/
  def interp {ε1 ε2 ρ} (handler : ε1 ⟹ CTree ε2) (t : CTree ε1 ρ) : CTree ε2 ρ :=
    corec' (fun {X} rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ => .inl <| ret v
      | ⟨.tau, t⟩ => .inr <| tau' <| rec (t _fin0)
      | ⟨.vis α e, k⟩ =>
        let he := handler e
        let x := fun (i : α) => rec (k <| .up i)

        let k := handler e >>= fun i =>
          let res := rec (k <| .up i)
          sorry
        .inl k
      | ⟨.zero, _⟩ => .inl zero
      | ⟨.choice, cs⟩ => .inr <| choice' (rec <| cs _fin0) (rec <| cs _fin1)
    ) t

end CTree
