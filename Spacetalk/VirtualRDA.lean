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

  -- What if nodes record other nodes
  -- Can the translation prevent deadlock
  -- what are the ways in which deadlock can be introduced
  -- is there a finite set of ways to introduce deadlock
  -- reason about which fifos are safe to merge and which are not
  -- Why are we failing, is it because of the program being bad,
  -- or the proof infrastructure introducing issues
  -- Differentiate hardware resource limit (lack of resource without introducing deadlock), 
  -- or program error

  -- Buffer sizes will be modeled later
  -- Maybe explicitly separate outputs
  -- Given that one node might not be able to emit N streams
  -- Find ways to tie back to original program
  -- FUTURE: Conditional read and write (for reductions)
  -- Use special node types for external producer/consumer
  -- Use membership constructor for external io
  structure FIFO (inputs outputs : List Ty) (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes ⊕ Member ty inputs
    consumer : Fin num_nodes ⊕ Member ty outputs

  def FIFOList (inputs outputs : List Ty) (num_nodes num_fifos : Nat) :=
    Vector (FIFO inputs outputs num_nodes) num_fifos

  def find_node_inputs (fifos : FIFOList ni no nn nf) (nid : Fin nn) : List Ty :=
    let filtered := fifos.toList.filter (match ·.consumer with | .inl node_id => node_id == nid | .inr _ => false)
    filtered.map (·.ty)

  def find_node_outputs (fifos : FIFOList ni no nn nf) (nid : Fin nn) : List Ty :=
    let filtered := fifos.toList.filter (match ·.producer with | .inl node_id => node_id == nid | .inr _ => false)
    filtered.map (·.ty)

  -- structure Compute (inputs outputs : List Ty) where
  --   pipeline : NodeOps inputs outputs
  
  -- structure Memory (ty : Ty) where
  --   size : Nat
  --   initial_value : Vector ty.denote size
  
  -- inductive Node : List Ty → List Ty → Type
  --   | compute : Compute inputs outputs → Node inputs outputs
  

  -- zeroed out vs non initialized memory

  -- The circuit is a steam → stream
  -- Special delay nodes to break cycles
  -- simple memory nodes
  structure Node (fifos : FIFOList ni no nn nf) (nid : Fin nn) where
    state : List Ty
    initial_state : TysHL state
    state_transform : NodeOps (state ++ (find_node_inputs fifos nid)) state
    pipeline : NodeOps (state ++ (find_node_inputs fifos nid)) (find_node_outputs fifos nid)

  -- First node is the initial node and last node is the terminal node
  def NodeList (fifos : FIFOList ni no nn nf) :=
    (nid : Fin nn) → Node fifos nid

  structure VirtualRDA where
    inputs: List Ty
    outputs : List Ty
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList inputs outputs num_nodes num_fifos
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

    def fifo_type (vrda : VirtualRDA) :=
      FIFO vrda.inputs vrda.outputs vrda.num_nodes

    def nth_output (vrda : VirtualRDA)
      (input_stream : TysHLS vrda.inputs) (n : Nat) (fifo : vrda.fifo_type) : fifo.ty.denote :=
      sorry

    @[simp] def denote (vrda : VirtualRDA) :
      TysHLS vrda.inputs → TysHLS vrda.outputs :=
      λ input_stream => λ n =>
        let output_fifos := vrda.fifos.toList.filter (match ·.consumer with | .inl _ => false | .inr _ => true)
        let output_func := vrda.nth_output input_stream n
        HList.from_list (·.ty) output_func output_fifos

  end VirtualRDA

end VirtualRDA
