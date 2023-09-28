import Mathlib.Data.Stream.Defs
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

  inductive BinOp : Ty → Ty → Type
    | plus : BinOp (.nat × .nat) .nat

  -- Exprs operate on not streams
  -- Progs operate on streams and are always stream(s) → stream(s)
  -- This is so that a final program is always a function from stream(s) to stream(s)

  inductive Expr : Ty → Type
    | const : Nat → Expr .nat
    | binop : BinOp α β → Expr (α → β)

  -- Cannot encode filter on infinite streams
  -- Filters must be done "locally"
  inductive Prog : Ty → Type
    | zip : Prog ((.stream α × .stream β) → .stream (α × β))
    | map : Expr (α → β) → Prog (.stream α → .stream β)
    | comp : Prog (α → β) → Prog (β → γ) → Prog (α → γ)

  -- Semantics

  @[reducible] def Ty.denote : Ty → Type
    | nat => Nat
    | prod α β => α.denote × β.denote
    | fn α β => α.denote → β.denote
    | stream ty => Stream' ty.denote

  @[simp] def BinOp.denote : BinOp α β → (α.denote → β.denote)
    | plus => λ (a, b) => a + b

  @[simp] def Expr.denote : Expr ty → ty.denote
    | const n => n
    | binop op => op.denote

  @[simp] def Prog.denote : Prog ty → ty.denote
    | zip => λ (sa, sb) => Stream'.zip (·, ·) sa sb
    | map f => λ s => Stream'.map f.denote s
    | comp f g => g.denote ∘ f.denote

  namespace Example
    -- A rudimentary a + b example
    def adder : Prog ((.stream .nat × .stream .nat) → .stream .nat) :=
      .comp  .zip (.map (.binop .plus))

    def adder' (tup : Stream' Nat × Stream' Nat) : Stream' Nat :=
      λ n => (tup.fst.nth n) + (tup.snd.nth n)

    def sa : Stream' Nat := id
    def sb : Stream' Nat := id

    def add := adder.denote (sa, sb)
    def add' := adder' (sa, sb)
    #eval add.nth 5
    #eval add'.nth 5

    theorem adder_equiv : adder.denote = adder' := by
      repeat {
        apply funext
        intros
        simp [adder', Stream'.map, Stream'.zip, Stream'.nth]
      }
  end Example

end Spatium

-- (Virtual) RDA Spec
-- Q: What optimizations should we do at this level?
-- A: A form of CSE: What Ben briefly worked on (function circuits).
namespace VirtFlow

  -- Syntax

  inductive Ty
    | unit
    | nat

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | nat => Nat

  -- More expressive adds that choose inputs with Fins
  -- monotonic to preserver old inputs
  inductive NodeOps : List Ty → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | add : NodeOps [.nat, .nat] [.nat]
    | dup : NodeOps [.nat] [.nat, .nat]
    | tail : NodeOps α α.tail
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

  -- We choose to denote a List Ty with a tuple instead of a heterogenous list 
  @[reducible] def ty_list_denote : List Ty → Type
    | [] => Unit
    | ty :: [] => ty.denote
    | ty :: tail => ty.denote × (ty_list_denote tail)

  -- Marker type for external input/outputs
  structure External where

  -- Buffer sizes will be modeled later
  -- Maybe explicitly separate outputs
  -- Given that one node might not be able to emit N streams
  -- Find ways to tie back to original program
  -- FUTURE: Conditional read and write (for reductions)
  -- Use special node types for external producer/consumer
  structure FIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes ⊕ External
    consumer : Fin num_nodes ⊕ External

  def find_node_inputs (fifos : Vector (FIFO num_nodes) num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (match ·.consumer with | .inl node_id => node_id == id | .inr _ => false)
    filtered.map (·.ty)

  def find_node_outputs (fifos : Vector (FIFO num_nodes) num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (match ·.producer with | .inl node_id => node_id == id | .inr _ => false)
    filtered.map (·.ty)

  def FIFOList (num_nodes num_fifos : Nat) := Vector (FIFO num_nodes) num_fifos

  -- The circuit is a steam → stream
  structure Node (fifos : FIFOList num_nodes num_fifos) (id : Fin num_nodes) where
    state : List Ty
    initial_state : ty_list_denote state
    state_transform : NodeOps (state ++ (find_node_inputs fifos id)) state
    pipeline : NodeOps (state ++ (find_node_inputs fifos id)) (find_node_outputs fifos id)

  -- First node is the initial node and last node is the terminal node
  def NodeList (fifos : FIFOList num_nodes num_fifos) :=
    (id : Fin num_nodes) → Node fifos id

  structure VirtFlowConfig where
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList num_nodes num_fifos 
    nodes : NodeList fifos

  -- Semantics

  @[simp] def node_ops_tail_denote (l : ty_list_denote α) : ty_list_denote α.tail :=
    match α with
      | [] => ()
      | _ :: [] => ()
      | _ :: _ :: _ => l.snd
  
  @[simp] def NodeOps.denote : NodeOps α β → (ty_list_denote α → ty_list_denote β)
    | nop => id
    | add => λ (a, b) => a + b
    | dup => λ x => (x, x)
    | tail => node_ops_tail_denote
    | comp f g => g.denote ∘ f.denote
  
  def find_graph_inputs (vfc : VirtFlowConfig) : List Ty :=
    let filtered := vfc.fifos.toList.filter (match ·.producer with | .inr _ => true | .inl _ => false)
    filtered.map (·.ty)
  
  def find_graph_outputs (vfc : VirtFlowConfig) : List Ty :=
    let filtered := vfc.fifos.toList.filter (match ·.consumer with | .inr _ => true | .inl _ => false)
    filtered.map (·.ty)
  
  @[reducible] def ty_list_to_streams : List Ty → Type
    | [] => Unit
    | ty :: [] => Stream' ty.denote
    | ty :: tail => Stream' ty.denote × (ty_list_to_streams tail)

  @[reducible] def VirtFlowConfig.type_denote (vfc : VirtFlowConfig) : Type :=
    (ty_list_to_streams (find_graph_inputs vfc)) → (ty_list_to_streams (find_graph_outputs vfc))

  @[simp] def VirtFlowConfig.denote (vfc : VirtFlowConfig) : vfc.type_denote :=
    λ inps =>
    sorry

end VirtFlow
