import Spacetalk.HList
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Vector

-- (Virtual) RDA Spec
-- Q: What optimizations should we do at this level?
-- A: A form of CSE: What Ben briefly worked on (function circuits).
namespace VirtualRDA

  -- Syntax

  inductive Ty
    | unit
    | nat

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | nat => Nat

  abbrev TysHL (tys : List Ty) := HList Ty.denote tys

  abbrev TysHLS (tys : List Ty) := Stream' (TysHL tys)

  -- More expressive adds that choose inputs with Fins
  -- monotonic to preserver old inputs
  inductive NodeOps : List Ty → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | add : NodeOps [.nat, .nat] [.nat]
    | dup : NodeOps [α] [α, α]
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

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

  def FIFOList (num_nodes num_fifos : Nat) := Vector (FIFO num_nodes) num_fifos

  def find_node_inputs (fifos : FIFOList num_nodes num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (match ·.consumer with | .inl node_id => node_id == id | .inr _ => false)
    filtered.map (·.ty)

  def find_node_outputs (fifos : FIFOList num_nodes num_fifos) (id : Fin num_nodes) : List Ty :=
    let filtered := fifos.toList.filter (match ·.producer with | .inl node_id => node_id == id | .inr _ => false)
    filtered.map (·.ty)

  -- The circuit is a steam → stream
  structure Node (fifos : FIFOList num_nodes num_fifos) (nid : Fin num_nodes) where
    state : List Ty
    initial_state : TysHL state
    state_transform : NodeOps (state ++ (find_node_inputs fifos nid)) state
    pipeline : NodeOps (state ++ (find_node_inputs fifos nid)) (find_node_outputs fifos nid)

  -- First node is the initial node and last node is the terminal node
  def NodeList (fifos : FIFOList num_nodes num_fifos) :=
    (id : Fin num_nodes) → Node fifos id

  structure VirtualRDA where
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList num_nodes num_fifos 
    nodes : NodeList fifos

  -- Semantics

  @[simp] def NodeOps.denote : NodeOps α β → (TysHL α → TysHL β)
    | nop => id
    | add => λ (a :: b :: []) => (a + b) :: []
    | dup => λ (a :: []) => a :: a :: []
    | comp f g => g.denote ∘ f.denote
  
  namespace Node

    def state_stream (node : Node fifos nid) (inputs : TysHLS (find_node_inputs fifos nid)) : TysHLS node.state
      | 0 => node.initial_state
      | n + 1 =>
        let prev_state := node.state_stream inputs n
        let curr_input := prev_state.append (inputs n)
        node.state_transform.denote curr_input

    @[simp] def denote (node : Node fifos nid) :
      TysHLS (find_node_inputs fifos nid) → TysHLS (find_node_outputs fifos nid) :=
      λ inputs =>
        let state_stream := node.state_stream inputs
        λ n =>
          let curr_state := state_stream n
          let curr_inputs := inputs n
          let combined_inputs := curr_state ++ curr_inputs
          node.pipeline.denote combined_inputs

  end Node

  namespace VirtualRDA

    def find_graph_inputs (vrda : VirtualRDA) : List Ty :=
      let filtered := vrda.fifos.toList.filter (match ·.producer with | .inr _ => true | .inl _ => false)
      filtered.map (·.ty)

    def find_output_fifos (vrda : VirtualRDA) : List (FIFO vrda.num_nodes) :=
      vrda.fifos.toList.filter (match ·.consumer with | .inr _ => true | .inl _ => false)
  
    def nth_output (vrda : VirtualRDA) (input_stream : TysHLS vrda.find_graph_inputs) (n : Nat) :
      (fifo : FIFO vrda.num_nodes) → fifo.ty.denote :=
      sorry

    @[simp] def denote (vrda : VirtualRDA) :
      TysHLS vrda.find_graph_inputs → TysHLS (vrda.find_output_fifos.map (·.ty)) :=
      λ input_stream => λ n =>
        HList.from_list (·.ty) (vrda.nth_output input_stream n) vrda.find_output_fifos

  end VirtualRDA

end VirtualRDA
