import Spacetalk.Stream
import Spacetalk.HList
import Spacetalk.Graph

-- Source Lang
namespace Step

------------------ Syntax ------------------
inductive Ty
  | bitVec : Nat → Ty
  deriving DecidableEq

@[reducible]
def Ty.denote : Ty → Type
  | bitVec w => BitVec w

def Ty.default : (ty : Ty) → ty.denote
  | bitVec _ => 0

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

-- inductive Ty
--   | stream : Prim → Ty
--   deriving DecidableEq

-- @[simp]
-- def Ty.prim : Ty → Prim
--   | stream p => p

-- @[reducible]
-- def Ty.denote : Ty → Type
  -- | stream p => Stream' p.denote

-- abbrev TysInput (tys : List Ty) := HList Ty.denote tys

inductive BinaryOp : Ty → Ty → Ty → Type
  | add : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)
  | mul : {w : Nat} → BinaryOp (.bitVec w) (.bitVec w) (.bitVec w)

inductive UnaryOp : Ty → Ty → Type
  | addConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)
  | mulConst : {w : Nat} → BitVec w → UnaryOp (.bitVec w) (.bitVec w)

inductive Prog : List Ty → Ty → Type
  | const : (α : Ty) → Prog [α] α
  | zip : BinaryOp α β γ → Prog aInp α → Prog bInp β → Prog (aInp ++ bInp) γ
  | map : UnaryOp α β → Prog inp α → Prog inp β
  | reduce : BinaryOp α β α → Nat → α.denote → Prog inp β → Prog inp α

------------------ Semantics ------------------
def BinaryOp.denote : BinaryOp α β γ → α.denote → β.denote → γ.denote
  | BinaryOp.add => BitVec.add
  | BinaryOp.mul => BitVec.mul

def UnaryOp.denote : UnaryOp α β → α.denote → β.denote
  | UnaryOp.addConst c => BitVec.add c
  | UnaryOp.mulConst c => BitVec.mul c

def Prog.denote {inputs : List Ty} {α : Ty} : Prog inputs α → (DenoStreamsList inputs → DenoStreamsList [α])
  | .const _ => λ ([a]ₕ) ↦ [a]ₕ
  | .zip op as bs => λ inp ↦ let (aInp, bInp) := inp.split; [Stream'.zip op.denote (as.denote aInp).head (bs.denote bInp).head]ₕ
  | .map op as => λ inp ↦ [Stream'.map op.denote (as.denote inp).head]ₕ
  | .reduce op n init bs => λ inp ↦ [Stream'.reduce op.denote n init (bs.denote inp).head]ₕ
end Step
