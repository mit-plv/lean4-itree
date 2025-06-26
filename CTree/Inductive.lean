import Mathlib.Data.Seq.Seq

mutual

inductive CTree (ε : Type → Type) (ρ : Type)
  | ret (v : ρ)
  | vis {α : Type} (e : ε α) (k : α → CTree ε ρ)
  | tau (t : CTreeInf ε ρ)

inductive CTreeInf (ε : Type → Type) (ρ : Type)
  | mk (t : Stream' (CTree ε ρ))
  -- This doesn't work
  -- | mk (t : Stream'.Seq (CTree ε ρ))

end
