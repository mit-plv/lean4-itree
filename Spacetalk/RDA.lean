import Spacetalk.Graph

inductive Ty
  | unit
  | nat
  | option : Ty → Ty
deriving DecidableEq

@[reducible] def Ty.denote : Ty → Type
  | unit => Unit
  | nat => Nat
  | option ty => Option ty.denote

def Ty.default : (ty : Ty) → ty.denote
  | unit => ()
  | nat => 0
  | option _ => none

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

inductive RDAOps : (inputs : List Ty) → (outputs : List Ty) → (state : List Ty) → Type
  | nop : RDAOps [] [] []

def RDAOps.eval {inputs outputs state : List Ty} (ops : RDAOps inputs outputs state) :
  DenoList inputs → DenoList state → (DenoList outputs) × (DenoList state) :=
  match ops with
    | nop => λ _ _ => ([], [])

instance : NodeOps RDAOps where
  eval := RDAOps.eval

def RDA := DataflowGraph Ty RDAOps

#check (⟨[], [], 0, .nil, []⟩ : RDA)
