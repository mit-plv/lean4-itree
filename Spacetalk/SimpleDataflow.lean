import Spacetalk.Graph

inductive Prim
  | bitVec : Nat → Prim
deriving DecidableEq

inductive Ty
  | prim : Prim → Ty
  | option : Prim → Ty
deriving DecidableEq

@[reducible] def Prim.denote : Prim → Type
  | bitVec w => BitVec w

def Prim.default : (p : Prim) → p.denote
  | bitVec _ => 0

@[reducible] def Ty.denote : Ty → Type
  | prim p => p.denote
  | option p => Option p.denote

def Ty.default : (ty : Ty) → ty.denote
  | .prim p => p.default
  | .option _ => none

def Ty.denoteBEq : (ty : Ty) → (ty.denote → ty.denote → Bool)
  | .prim _ => λ a b => a = b
  | .option _ => λ a b =>
    match a, b with
      | .some aa, .some bb => aa == bb
      | .none, .none => true
      | _, _ => false

instance {ty : Ty} : BEq ty.denote where
  beq := ty.denoteBEq

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

def BitVecTy (w : Nat) := Ty.prim (Prim.bitVec w)

inductive BinaryOp : Ty → Ty → Ty → Type
  | add : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
  | mul : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
  | eq : BinaryOp α α (BitVecTy 1)

def BinaryOp.eval : BinaryOp α β γ → (α.denote → β.denote → γ.denote)
  | add => BitVec.add
  | mul => BitVec.mul
  | eq => λ a b => if a == b then ⟨1, by simp⟩ else ⟨0, by simp⟩

inductive UnaryOp : Ty → Ty → Type
  | id : UnaryOp α α
  | binOpLeftConst : BinaryOp α β γ → α.denote → UnaryOp β γ
  | binOpRightConst : BinaryOp α β γ → β.denote → UnaryOp α γ

def UnaryOp.eval : UnaryOp α β → (α.denote → β.denote)
  | id => (·)
  | binOpLeftConst bOp a => (bOp.eval a ·)
  | binOpRightConst bOp b => (bOp.eval · b)

inductive Pipeline : (inputs : List Ty) → (outputs : List Ty) → Type
  | const : {α : Ty} → α.denote → Pipeline [] [α]
  | unaryOp : {α β : Ty} → UnaryOp α β → Pipeline [α] [β]
  | binaryOp : {α β γ : Ty} → BinaryOp α β γ → Pipeline [α, β] [γ]
  | comp : {α β γ : List Ty} → Pipeline β γ → Pipeline α β → Pipeline α γ

def Pipeline.eval : Pipeline α β → (DenoList α → DenoList β)
  | const a => λ _ => [a]ₕ
  | unaryOp op => λ ([a]ₕ) => [op.eval a]ₕ
  | binaryOp op => λ ([a, b]ₕ) => [op.eval a b]ₕ
  | comp f g => f.eval ∘ g.eval

def Ops (inputs outputs state : List Ty) :=
  Pipeline (inputs ++ state) (outputs ++ state)

instance : NodeOps Ops where
  eval := λ pipeline inputs state => (pipeline.eval (inputs ++ₕ state)).split

def DataflowMachine := DataflowGraph Ty Ops
