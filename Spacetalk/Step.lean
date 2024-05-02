import Spacetalk.Stream
import Spacetalk.HList

-- Source Lang
namespace Step

------------------ Syntax ------------------
inductive Prim
  | bitVec : Nat → Prim
  deriving DecidableEq

@[reducible]
def Prim.denote : Prim → Type
  | bitVec w => BitVec w

inductive Ty
  | stream : Prim → Ty
  deriving DecidableEq

@[simp]
def Ty.prim : Ty → Prim
  | stream p => p

infixr:25 " → " => Ty.fn

@[reducible]
def Ty.denote : Ty → Type
  | stream p => Stream' p.denote

abbrev TysInput (tys : List Ty) := HList Ty.denote tys

inductive BinaryOp : Prim → Prim → Prim → Type
  | add : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)
  | mul : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)

inductive UnaryOp : Prim → Prim → Type
  | addConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)
  | mulConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)

inductive Prog : List Ty → Ty → Type
  | const : (α : Ty) → Prog [α] α
  | zip : BinaryOp α β γ → Prog aInp (.stream α) → Prog bInp (.stream β) → Prog (aInp ++ bInp) (.stream γ)
  | map : UnaryOp α β → Prog inp (.stream α) → Prog inp (.stream β)
  | reduce : BinaryOp α β α → Nat → α.denote → Prog inp (.stream β) → Prog inp (.stream α)

------------------ Semantics ------------------
def BinaryOp.denote : BinaryOp α β γ → α.denote → β.denote → γ.denote
  | BinaryOp.add => BitVec.add
  | BinaryOp.mul => BitVec.mul

def UnaryOp.denote : UnaryOp α β → α.denote → β.denote
  | UnaryOp.addConst c => BitVec.add c
  | UnaryOp.mulConst c => BitVec.mul c

def Prog.denote {inputs : List Ty} {α : Ty} : Prog inputs α → (TysInput inputs → TysInput [α])
  | .const _ => λ ([a]ₕ) ↦ [a]ₕ
  | .zip op as bs => λ inp ↦ let (aInp, bInp) := inp.split; [Stream'.zip op.denote (as.denote aInp).head (bs.denote bInp).head]ₕ
  | .map op as => λ inp ↦ [Stream'.map op.denote (as.denote inp).head]ₕ
  | .reduce op n init bs => λ inp ↦ [Stream'.reduce op.denote n init (bs.denote inp).head]ₕ
end Step
