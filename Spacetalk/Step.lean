import Spacetalk.Stream

-- Source Lang
namespace Step

  ------------------ Syntax ------------------

  inductive Prim
    | bitVec : Nat → Prim
  deriving DecidableEq

  @[reducible] def Prim.denote : Prim → Type
    | bitVec w => BitVec w

  inductive Ty
    | prim : Prim → Ty
    | stream : Prim → Ty
    | fn : Ty → Ty → Ty
  deriving DecidableEq

  infixr:25 " → " => Ty.fn

  abbrev BitVecTy (w : Nat) := Ty.prim (Prim.bitVec w)

  @[reducible] def Ty.denote : Ty → Type
    | prim p => p.denote
    | stream p => Stream' p.denote
    | fn α β => α.denote → β.denote

  inductive BinaryOp : Prim → Prim → Prim → Type
    | add : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)
    | mul : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)

  inductive UnaryOp : Prim → Prim → Type
    | addConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)
    | mulConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)

  inductive Prog : Ty → Type
    | zip : BinaryOp α β γ → Prog (.stream α → .stream β → .stream γ)
    | map : UnaryOp α β → Prog (.stream α → .stream β)
    | reduce : BinaryOp α β α → Nat → α.denote → Prog (.stream β → .stream α)
    | comp : {α β γ : Ty} → Prog (β → γ) → Prog (α → β) → Prog (α → γ)
    | comp2 : {α β γ δ : Ty} → Prog (γ → δ) → Prog (α → β → γ) → Prog (α → β → δ)

  ------------------ Semantics ------------------

  def BinaryOp.denote : BinaryOp α β γ → α.denote → β.denote → γ.denote
    | BinaryOp.add => BitVec.add
    | BinaryOp.mul => BitVec.mul

  def UnaryOp.denote : UnaryOp α β → α.denote → β.denote
    | UnaryOp.addConst c => BitVec.add c
    | UnaryOp.mulConst c => BitVec.mul c

  def Prog.denote {α : Ty} : Prog α → α.denote
    | Prog.zip op => Stream'.zip op.denote
    | Prog.map op => Stream'.map op.denote
    | Prog.reduce op n init => Stream'.reduce op.denote n init
    | Prog.comp f g => f.denote ∘ g.denote
    | Prog.comp2 f g => λ a b => f.denote (g.denote a b)

end Step
