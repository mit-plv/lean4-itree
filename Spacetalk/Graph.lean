import Mathlib.Data.Vector
import Mathlib.Data.Stream.Defs

import Spacetalk.HList

class Denote (τ : Type) [DecidableEq τ] where
  denote : τ → Type

abbrev DenoList {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) := HList Denote.denote ts

abbrev DenoStream {τ : Type} [DecidableEq τ] [Denote τ] (t : τ) := Stream' (Denote.denote t)

abbrev DenoStreamsList {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) := HList DenoStream ts

abbrev DenoListsStream {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) := Stream' (DenoList ts)

@[simp] def DenoStreamsList.pack {τ : Type} [DecidableEq τ] [Denote τ] {ts : List τ} (dsl : DenoStreamsList ts) : DenoListsStream ts :=
  match ts with
    | [] => λ _ => []
    | h::t =>
      λ n =>
        let h_elem : (Denote.denote h) := (dsl.get .head) n
        let tail_streams : DenoStreamsList t :=
          match dsl with
            | _ :: rest => rest
        h_elem :: (pack tail_streams) n

@[simp] def DenoListsStream.unpack {τ : Type} [DecidableEq τ] [Denote τ] {ts : List τ} (dls : DenoListsStream ts) : DenoStreamsList ts :=
  match ts with
    | [] => []
    | h::t =>
      let h_stream : Stream' (Denote.denote h) := λ n => (dls n).get .head
      let t_stream : DenoListsStream t := λ n =>
        match dls n with
          | _ :: rest => rest
      h_stream :: unpack t_stream

theorem DenoStreamsList_pack_unpack_eq {τ : Type} [DecidableEq τ] [Denote τ] {ts : List τ} {dsl : DenoStreamsList ts}
  : dsl.pack.unpack = dsl := by
  induction dsl <;> simp; assumption

theorem DenoListsStream_unpack_pack_eq {τ : Type} [DecidableEq τ] [Denote τ] {ts : List τ} {dls : DenoListsStream ts}
  : dls.unpack.pack = dls := by
  apply funext
  intro n
  induction ts
  case nil => simp; cases dls n; rfl
  case cons h t ih =>
    simp
    cases hm : dls n with
    | cons hh tt =>
      apply (HList.cons.injEq _ _ _ _).mpr
      apply And.intro
      · simp
      · have : tt = (match dls · with | _ :: rest => rest) n := by
          simp
          rw [hm]
        rw [this]
        exact ih

abbrev NodeType (τ : Type) [DecidableEq τ][Denote τ] :=
  (inputs : List τ) → (outputs : List τ) → (state : List τ) → Type

class NodeOps {τ : Type} [DecidableEq τ][Denote τ] (F : NodeType τ) where
  eval : F inputs outputs state → DenoList inputs → DenoList state → (DenoList outputs × DenoList state)

structure Node (τ : Type) [DecidableEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  state : List τ
  initialState : DenoList state
  ops : F inputs outputs state

def NodeList (τ : Type) [DecidableEq τ][Denote τ] (F : NodeType τ) [NodeOps F] (numNodes : Nat) :=
  Vector (Node τ F) numNodes

structure InputFIFO {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
  (inputs : List τ) (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Member t inputs
  consumer : Fin numNodes
  consumerPort: Member t (nodes.get consumer).inputs

structure OutputFIFO {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
  (outputs : List τ) (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumer : Member t outputs

structure AdvancingFIFO {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
  (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs
  adv : producer < consumer

structure InitializedFIFO {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
  (nodes : NodeList τ F numNodes) where
  t : τ
  initialValue : Denote.denote t
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs

inductive FIFO {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
  {numNodes : Nat} (inputs outputs : List τ) (nodes : NodeList τ F numNodes)
  | input : InputFIFO inputs nodes → FIFO inputs outputs nodes
  | output : OutputFIFO outputs nodes → FIFO inputs outputs nodes
  | advancing : AdvancingFIFO nodes → FIFO inputs outputs nodes
  | initialized : InitializedFIFO nodes → FIFO inputs outputs nodes

namespace FIFO

  @[simp] def t {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → τ
    | .input f | .output f | .advancing f | .initialized f => f.t

  @[simp] def isInput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → Bool
    | .input _ => true
    | _ => false

  @[simp] def isOutput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → Bool
    | .output _ => true
    | _ => false

  theorem outputNotInput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    {fifo : FIFO inputs outputs nodes}
    : fifo.isOutput = true → fifo.isInput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp | simp [h_match] at h)

  theorem inputNotOutput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    {fifo : FIFO inputs outputs nodes}
    : fifo.isInput = true → fifo.isOutput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp | simp [h_match] at h)

  def producer {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → fifo.isInput = false → Fin numNodes
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producer

  def producerPort {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → (h : fifo.isInput = false) → Member fifo.t (nodes.get (fifo.producer h)).outputs
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producerPort

  def consumer {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → fifo.isOutput = false → Fin numNodes
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumer

  def consumerPort {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] {numNodes : Nat} {nodes : NodeList τ F numNodes} {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → (h : fifo.isOutput = false) → Member fifo.t (nodes.get (fifo.consumer h)).inputs
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumerPort

end FIFO

structure DataflowGraph (τ : Type) [DecidableEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  numNodes : Nat
  nodes : NodeList τ F numNodes
  fifos : List (FIFO inputs outputs nodes)

namespace Node

end Node

namespace DataflowGraph

  def FIFOType {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
    (dfg : DataflowGraph τ F) := FIFO dfg.inputs dfg.outputs dfg.nodes

  def isNodeInput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
    {dfg : DataflowGraph τ F} {nid : Fin dfg.numNodes} {t : τ}
    (port : Member t (dfg.nodes.get nid).inputs) (fifo : dfg.FIFOType) : Bool :=
    match fifo with
      | .input fifo' | .initialized fifo' | .advancing fifo' =>
        if h : fifo'.consumer = nid ∧ fifo'.t = t then
          h.left ▸ h.right ▸ fifo'.consumerPort == port
        else
          false
      | _ => false

  def isGlobalOutput {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F]
    {dfg : DataflowGraph τ F} {t : τ}
    (output : Member t dfg.outputs) (fifo : dfg.FIFOType) : Bool :=
    match fifo with
      | .output fifo' =>
        if h : fifo'.t = t then
          h ▸ fifo'.consumer == output
        else
          false
      | _ => false

  def stateMap {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] (dfg : DataflowGraph τ F) :=
    (nid : Fin dfg.numNodes) → (DenoList (dfg.nodes.get nid).outputs) × (DenoList (dfg.nodes.get nid).state)

  def nthCycleState {τ : Type} [DecidableEq τ] [Denote τ] {F : NodeType τ} [NodeOps F] (dfg : DataflowGraph τ F)
    (inputs : TysHListStream vrda.inputs) (n : Nat) : vrda.stateMap :=
    λ nid =>
      let node := vrda.nodes.get nid
      let inputsFinRange := List.finRange node.inputs.length
      have finRange_map_eq : inputsFinRange.map node.inputs.get = node.inputs := by simp [List.get]
      let nodeInputs : (TysHList node.inputs) := finRange_map_eq ▸ inputsFinRange.toHList node.inputs.get (
        λ fin =>
          let port := node.inputs.nthMember fin
          let fifoOpt := vrda.fifos.find? (vrda.isNodeInput port)
          match h_match : fifoOpt with
            | .some fifo =>
              have h_is_node_input : vrda.isNodeInput port fifo = true := List.find?_some h_match
              have h_ty_eq : fifo.ty = node.inputs.get fin := by
                cases h_fm : fifo <;> simp [h_fm, VirtualRDA.isNodeInput] at h_is_node_input <;>
                (
                  rename_i fifo'
                  have p : fifo'.consumer = nid ∧ fifo'.ty = (vrda.nodes.get nid).inputs.get fin := by
                    apply (dite_eq_iff.mp h_is_node_input).elim
                    · intro e
                      exact e.fst
                    · intro e
                      have := e.snd
                      contradiction
                  exact p.right
                )
              match fifo with
                | .input fifo' =>
                  h_ty_eq ▸ (inputs n).get fifo'.producer
                | .advancing fifo' =>
                  have : fifo'.producer < nid := by
                    have : fifo'.consumer = nid := by
                      simp [VirtualRDA.isNodeInput] at h_is_node_input
                      have p : fifo'.consumer = nid ∧ fifo'.ty = (vrda.nodes.get nid).inputs.get fin := by
                        apply (dite_eq_iff.mp h_is_node_input).elim
                        · intro e
                          exact e.fst
                        · intro e
                          have := e.snd
                          contradiction
                      exact p.left
                    rw [←this]
                    exact fifo'.adv
                  let producerOutputs := (vrda.nthCycleState inputs n fifo'.producer).fst
                  h_ty_eq ▸ producerOutputs.get fifo'.producerPort
                | .initialized fifo' =>
                  match n with
                    | 0 => h_ty_eq ▸ fifo'.initialValue
                    | n' + 1 =>
                      let producerOutputs := (vrda.nthCycleState inputs n' fifo'.producer).fst
                      h_ty_eq ▸ producerOutputs.get fifo'.producerPort
            | .none =>
              (node.inputs.get fin).default
      )
      let currState : TysHList node.state :=
        match n with
         | 0 => node.initialState
         | n' + 1 => (vrda.nthCycleState inputs n' nid).snd
      let nodeOutputs := node.denote nodeInputs currState
      let nextState := node.nextState nodeInputs currState
      (nodeOutputs, nextState)
      termination_by nthCycleState _ _ n nid => (n, nid)

  def denote (vrda : VirtualRDA) (inputs : TyStreamsHList vrda.inputs)
                    : TyStreamsHList (vrda.outputs) :=
    let packedInputs := inputs.pack
    let stateStream := vrda.nthCycleState packedInputs
    let outputsFinRange := List.finRange vrda.outputs.length
    have finRange_map_eq : outputsFinRange.map vrda.outputs.get = vrda.outputs := by simp [List.get]
    let packedOutputStream : TysHListStream vrda.outputs :=
      λ n =>
        finRange_map_eq ▸ outputsFinRange.toHList vrda.outputs.get (
          λ fin =>
            let outputMem := vrda.outputs.nthMember fin
            let fifoOpt := vrda.fifos.find? (vrda.isGlobalOutput outputMem)
            match h_some : fifoOpt with
              | .some fifo =>
                have h_is_output : vrda.isGlobalOutput outputMem fifo = true := List.find?_some h_some
                have h_ty_eq : fifo.ty = vrda.outputs.get fin := by
                  cases h_fm : fifo <;> simp [h_fm, VirtualRDA.isGlobalOutput] at h_is_output
                  rename_i fifo'
                  apply (dite_eq_iff.mp h_is_output).elim
                  · intro e
                    exact e.fst
                  · intro e
                    have := e.snd
                    contradiction
                match fifo with
                  | .output fifo' =>
                    h_ty_eq ▸ (stateStream n fifo'.producer).fst.get fifo'.producerPort
              | .none =>
                (vrda.outputs.get fin).default
        )
    packedOutputStream.unpack

  -- How does this change the semantics?
  def connectFIFOs (vrda : VirtualRDA) (ty : Ty)
    (pi : Fin vrda.fifos.length) (ci : Fin vrda.fifos.length) (init : ty.denote)
    : VirtualRDA :=
    let pf := vrda.fifos.get pi
    let cf := vrda.fifos.get ci
    if h : pf.isOutput = true ∧ cf.isInput = true ∧ pf.ty = ty ∧ cf.ty = ty then
      let trimmedFifos := (vrda.fifos.remove pf).remove cf
      let h_ni : pf.isInput = false := pf.outputNotInput h.left
      let h_no : cf.isOutput = false := cf.inputNotOutput h.right.left
      let initFifo : InitializedFIFO vrda.nodes := {
        ty := ty,
        initialValue := init,
        producer := pf.producer h_ni,
        consumer := cf.consumer h_no,
        producerPort := h.right.right.left ▸ pf.producerPort h_ni,
        consumerPort := h.right.right.right ▸ cf.consumerPort h_no,
      }
      let newFifo : vrda.FIFOType := FIFO.initialized initFifo
      let newFifos := newFifo :: trimmedFifos
      { vrda with
        fifos := newFifos
      }
    else
      vrda

end DataflowGraph
