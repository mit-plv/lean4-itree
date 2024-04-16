import Spacetalk.Stream

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

infixr:25 " → " => Ty.fn

@[reducible]
def Ty.denote : Ty → Type
  | stream p => Stream' p.denote

inductive BinaryOp : Prim → Prim → Prim → Type
  | add : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)
  | mul : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)

inductive UnaryOp : Prim → Prim → Type
  | addConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)
  | mulConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)

inductive Prog : Ty → Type
  | const : (α : Ty) → α.denote → Prog α
  | zip : BinaryOp α β γ → Prog (.stream α) → Prog (.stream β) → Prog (.stream γ)
  | map : UnaryOp α β → Prog (.stream α) → Prog (.stream β)
  | reduce : BinaryOp α β α → Nat → α.denote → Prog (.stream β) → Prog (.stream α)

------------------ Semantics ------------------
def BinaryOp.denote : BinaryOp α β γ → α.denote → β.denote → γ.denote
  | BinaryOp.add => BitVec.add
  | BinaryOp.mul => BitVec.mul

def UnaryOp.denote : UnaryOp α β → α.denote → β.denote
  | UnaryOp.addConst c => BitVec.add c
  | UnaryOp.mulConst c => BitVec.mul c

def Prog.denote {α : Ty} : Prog α → α.denote
  | .const _ a => a
  | .zip op as bs => Stream'.zip op.denote as.denote bs.denote
  | .map op as => Stream'.map op.denote as.denote
  | .reduce op n init bs => Stream'.reduce op.denote n init bs.denote

def Prog.p : Prog α → List Nat
  | .const _ _ => [1]
  | .zip _ as bs => as.p ++ bs.p
  | .map _ as => as.p
  | .reduce _ _ _ bs => bs.p
end Step
