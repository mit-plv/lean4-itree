import Spacetalk.Graph

inductive Ty
  | unit
  | bool
  | nat
  | option : Ty → Ty
deriving DecidableEq

@[reducible] def Ty.denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat
  | option ty => Option ty.denote

def Ty.default : (ty : Ty) → ty.denote
  | unit => ()
  | bool => false
  | nat => 0
  | option _ => none

def Ty.denoteBEq : (ty : Ty) → (ty.denote → ty.denote → Bool)
  | .unit => (· == ·)
  | .bool => (· == ·)
  | .nat => (· == ·)
  | .option t => λ a b =>
    match a, b with
      | .some aa, .some bb => t.denoteBEq aa bb
      | .none, .none => true
      | _, _ => false

instance {ty : Ty} : BEq ty.denote where
  beq := ty.denoteBEq

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

instance : OfNat (Denote.denote Ty.nat) n where
  ofNat := n

inductive UnaryOp : Ty → Ty → Type
  | id : UnaryOp α α
  | incMod : Nat → UnaryOp .nat .nat
  | eqConst : α.denote → UnaryOp α .bool

def UnaryOp.eval : UnaryOp α β → (α.denote → β.denote)
  | id => (·)
  | incMod n => λ x => (x + 1) % n
  | eqConst x => (x == ·)

inductive BinaryOp : Ty → Ty → Ty → Type
  | add : BinaryOp .nat .nat .nat
  | mul : BinaryOp .nat .nat .nat
  | eq : BinaryOp α α .bool

def BinaryOp.eval : BinaryOp α β γ → (α.denote → β.denote → γ.denote)
  | add => HAdd.hAdd
  | mul => HMul.hMul
  | eq => BEq.beq

inductive Ops : (inputs : List Ty) → (outputs : List Ty) → (state : List Ty) → Type
  | unaryOp : UnaryOp α α → Ops [α] [α] state
  | binaryOp : BinaryOp α β γ → Ops [α, β] [γ] state
  | unaryStateOp : UnaryOp α α → Member α state → Ops [] [α] state
  | binaryStateOp : BinaryOp α β γ → Member β state → Ops [α] [γ] state
  | unaryStateUpdate : UnaryOp α α → Member α state → Ops inputs inputs state
  | binaryStateUpdate : BinaryOp α β α → Member α state → Ops [β] [] state
  | stateUnaryGuard : UnaryOp α .bool → Member α state → Ops [β] [.option β] state
  | stateReset : UnaryOp α .bool → Member α state → Member β state → β.denote → Ops inputs inputs state
  | comp : Ops β γ state → Ops α β state → Ops α γ state

def Ops.eval {inputs outputs state : List Ty} (ops : Ops inputs outputs state) :
  DenoList inputs → DenoList state → (DenoList outputs) × (DenoList state) :=
  match ops with
    | unaryOp uOp => λ (a :: []) currState => (uOp.eval a :: [], currState)
    | binaryOp bOp => λ (a :: b :: []) currState => (bOp.eval a b :: [], currState)
    | unaryStateOp uOp i => λ _ currState => (uOp.eval (currState.get i) :: [], currState)
    | binaryStateOp bOp i => λ (a :: []) currState => (bOp.eval a (currState.get i) :: [], currState)
    | unaryStateUpdate uOp i => λ ins currState => (ins, currState.replace i (uOp.eval (currState.get i)))
    | binaryStateUpdate bOp i => λ (b :: []) currState => ([], currState.replace i (bOp.eval (currState.get i) b))
    | stateUnaryGuard uOp i => λ (b :: []) currState => if uOp.eval (currState.get i) then (.some b :: [], currState) else (.none :: [], currState)
    | stateReset uOp i j val => λ ins currState => if uOp.eval (currState.get i) then (ins, currState.replace j val) else (ins, currState)
    | comp f g => λ ins currState => let (outs, state') := g.eval ins currState; f.eval outs state'

instance : NodeOps Ops where
  eval := Ops.eval

def DataflowMachine := DataflowGraph Ty Ops
