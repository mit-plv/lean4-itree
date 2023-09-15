import Mathlib.Data.Vector

-- Source Lang
namespace Spatium

  -- Syntax

  inductive Ty
    | nat
    | prod : Ty → Ty → Ty
    | fn : Ty → Ty → Ty
    | stream : Ty → Ty
  infixr:55 " × " => Ty.prod
  infixr:25 " → " => Ty.fn

  inductive Op : Ty → Ty → Type
    | plus : Op (.nat × .nat) .nat

  inductive Term : Ty → Type
    | const : Nat → Term .nat
    | op : Op α β → Term (α → β)
    | range : Term .nat → Term (.stream .nat)
    | zip : Term (.stream α) → Term (.stream β) → Term (.stream (α × β))
    | map : Term (α → β) → Term (.stream α) → Term (.stream β)

  -- Semantics

  @[reducible] def Ty.denote : Ty → Type
    | nat => Nat
    | prod α β => α.denote × β.denote
    | fn α β => α.denote → β.denote
    | stream ty => List ty.denote

  @[simp] def Op.denote : Op α β → (α.denote → β.denote)
    | plus => λ (a, b) => a + b

  @[simp] def Term.denote : Term ty → ty.denote
    | const x => x
    | op x => x.denote
    | range n => List.range n.denote
    | zip a b => List.zip a.denote b.denote
    | map f l => List.map f.denote l.denote

  namespace Example
    -- A rudimentary a + b example
    -- where a and b are two streams that range over [0-9]
    -- and a node c sums the two streams
    def a : Term (.stream .nat) := .range (.const 10)
    def b : Term (.stream .nat) := .range (.const 10)
    def zipper : Term (.stream (.nat × .nat)) := .zip a b
    def c : Term (.stream .nat) := .map (.op .plus) zipper

    def a_plus_b := (List.zip (List.range 10) (List.range 10)).map (λ (a, b) => a + b)

    example : c.denote = a_plus_b := by
      simp
  end Example

end Spatium

-- (Virtual) RDA Spec
-- What optimizations should we do at this level?
namespace VirtFlow

  -- Syntax

  inductive Ty
    | unit
    | nat
    | bool

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | bool => Bool
    | nat => Nat

  inductive NodeOps : List Ty → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | inc : NodeOps [.nat] [.nat]
    | add : NodeOps [.nat, .nat] [.nat]
    | sub : NodeOps [.nat, .nat] [.nat]
    | mul : NodeOps [.nat, .nat] [.nat]
    | dup : NodeOps [.nat] [.nat, .nat]
    | tail : NodeOps α α.tail
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

  -- We choose to denote a List Ty with a tuple instead of a heterogenous list 
  @[reducible] def ty_list_denote : List Ty → Type
    | [] => Unit
    | ty :: [] => ty.denote
    | ty :: tail => ty.denote × (ty_list_denote tail)

  -- Buffer sizes will be modeled later
  -- Special output fifo?
  -- Maybe explicitly separate outputs
  -- Given that one node might not be able to emit N streams
  -- Find ways to tie back to original program
  -- conditionally dequeable and enqueable, for reductions
  structure FIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes
  
  def find_inputs (fifos : Vector (FIFO num_nodes) num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (·.producer == id)
    filtered.map (·.ty)

  def find_outputs (fifos : Vector (FIFO num_nodes) num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (·.consumer == id)
    filtered.map (·.ty)

  -- State should need done signals
  -- Maybe separate state transforms
  structure Node (fifos : Vector (FIFO num_nodes) num_fifos) (id : Fin num_nodes) where
    state : List Ty
    initial_state : ty_list_denote state
    state_transform : NodeOps state state
    pipeline : NodeOps (state ++ (find_inputs fifos id)) (find_outputs fifos id)

  -- First node is the initial node and last node is the terminal node
  def NodeList {num_nodes num_fifos : Nat} (fifos : Vector (FIFO num_nodes) num_fifos) :=
    (id : Fin num_nodes) → Node fifos id

  structure VirtFlowConfig where
    num_nodes : Nat
    num_fifos : Nat
    fifos : Vector (FIFO num_nodes) num_fifos
    nodes : NodeList fifos

  -- Semantics

  @[simp] def node_ops_tail_denote (l : ty_list_denote α) : ty_list_denote α.tail :=
    match α with
      | [] => ()
      | _ :: [] => ()
      | _ :: _ :: _ => l.snd
  
  @[simp] def NodeOps.denote : NodeOps α β → (ty_list_denote α → ty_list_denote β)
    | nop => id
    | inc => (· + 1)
    | add => λ (a, b) => a + b
    | sub => λ (a, b) => a - b
    | mul => λ (a, b) => a * b
    | dup => λ x => (x, x)
    | tail => node_ops_tail_denote
    | comp f g => g.denote ∘ f.denote

end VirtFlow
