import Mathlib.Data.Vector
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Logic.Basic
import Std.Data.List.Lemmas

import Spacetalk.HList
import Spacetalk.Stream

inductive Ty
  | unit
  | nat
deriving BEq, DecidableEq

@[reducible] def Ty.denote : Ty → Type
  | unit => Unit
  | nat => Nat

def Ty.default : (ty : Ty) → ty.denote
  | unit => ()
  | nat => 0

instance {ty : Ty} : DecidableEq ty.denote :=
  λ a b =>
    match ty with
      | .unit => isTrue rfl
      | .nat => Nat.decEq a b

instance {ty : Ty} : Inhabited ty.denote where
  default := ty.default

abbrev TyStream (ty : Ty) := Stream' (ty.denote)

abbrev TyStreamsHList (tys : List Ty) := HList TyStream tys

abbrev TysHList (tys : List Ty) := HList Ty.denote tys

abbrev TysHListStream (tys : List Ty) := Stream' (TysHList tys)

def TyStreamsHList.pack (shl : TyStreamsHList tys) : TysHListStream tys :=
  match tys with
    | [] => λ _ => []
    | h::t =>
      λ n =>
        let h_elem : h.denote := (shl.get .head) n
        let tail_streams : TyStreamsHList t :=
          match shl with
            | _ :: rest => rest
        h_elem :: (pack tail_streams) n

def TysHListStream.unpack (s : TysHListStream tys) : TyStreamsHList tys :=
  match tys with
    | [] => []
    | h::t =>
      let h_stream : Stream' h.denote := λ n => (s n).get .head
      let t_stream : TysHListStream t := λ n =>
        match s n with
          | _ :: rest => rest
      h_stream :: unpack t_stream

inductive NodeOps : (inputs : List Ty) → List Ty → Type
  | nop : NodeOps α α -- for stateless nodes
  | dropAll : NodeOps α []
  | add : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
  | mul : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
  | select : (ty : Ty) → (a : Member ty inputs) → NodeOps inputs [ty]
  | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

structure Node where
  state : List Ty
  initialState : TysHList state
  inputs : List Ty
  outputs : List Ty
  stateTransform : NodeOps (state ++ inputs) state
  pipeline : NodeOps (state ++ inputs) outputs

def NodeList (numNodes : Nat) := Vector Node numNodes

structure InputFIFO (inputs : List Ty) (nodes : NodeList numNodes) where
  ty : Ty
  producer : Member ty inputs
  consumer : Fin numNodes
  consumerPort: Member ty (nodes.get consumer).inputs
deriving DecidableEq

structure OutputFIFO (outputs : List Ty) (nodes : NodeList numNodes) where
  ty : Ty
  producer : Fin numNodes
  producerPort: Member ty (nodes.get producer).outputs
  consumer : Member ty outputs
deriving DecidableEq

structure AdvancingFIFO (nodes : NodeList numNodes) where
  ty : Ty
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member ty (nodes.get producer).outputs
  consumerPort: Member ty (nodes.get consumer).inputs
  adv : producer < consumer
deriving DecidableEq

structure InitializedFIFO (nodes : NodeList numNodes) where
  ty : Ty
  initialValue : ty.denote
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member ty (nodes.get producer).outputs
  consumerPort: Member ty (nodes.get consumer).inputs

def aa : True ∧ True := ⟨trivial, trivial⟩

instance {nn : Nat} {nodes : NodeList nn} : DecidableEq (InitializedFIFO nodes) :=
  λ a b =>
    let eq := InitializedFIFO.mk.injEq a.ty a.initialValue a.producer a.consumer a.producerPort a.consumerPort b.ty b.initialValue b.producer b.consumer b.producerPort b.consumerPort
    if h_ty : a.ty = b.ty then
      have h_dety_eq := congr rfl h_ty
      if h_init : cast h_dety_eq a.initialValue = b.initialValue then
        have h_init_eq := heq_of_cast_eq h_dety_eq h_init
        if h_p : a.producer = b.producer then
          have h_ppty_eq := by rw[h_ty, h_p]
          if h_pp : cast h_ppty_eq a.producerPort = b.producerPort then
            have h_pp_eq := heq_of_cast_eq h_ppty_eq h_pp
            if h_c : a.consumer = b.consumer then
              have h_cpty_eq := by rw[h_ty, h_c]
              if h_cp : cast h_cpty_eq a.consumerPort = b.consumerPort then
                have h_cp_eq := heq_of_cast_eq h_cpty_eq h_cp
                isTrue (eq.mpr ⟨h_ty, h_init_eq, h_p, h_c, h_pp_eq, h_cp_eq⟩)
              else
                isFalse (λ h_eq => h_cp (cast_eq_iff_heq.mpr (eq.mp h_eq).right.right.right.right.right))
            else
              isFalse (λ h_eq => h_c (eq.mp h_eq).right.right.right.left)
          else
            isFalse (λ h_eq => h_pp (cast_eq_iff_heq.mpr (eq.mp h_eq).right.right.right.right.left))
        else
          isFalse (λ h_eq => h_p (eq.mp h_eq).right.right.left)
      else
        isFalse (λ h_eq => h_init (cast_eq_iff_heq.mpr (eq.mp h_eq).right.left))
    else
      isFalse (λ h_eq => h_ty (eq.mp h_eq).left)

inductive FIFO {numNodes : Nat} (inputs outputs : List Ty) (nodes : NodeList numNodes)
  | input : InputFIFO inputs nodes → FIFO inputs outputs nodes
  | output : OutputFIFO outputs nodes → FIFO inputs outputs nodes
  | advancing : AdvancingFIFO nodes → FIFO inputs outputs nodes
  | initialized : InitializedFIFO nodes → FIFO inputs outputs nodes
deriving DecidableEq

@[simp] def FIFO.ty : (fifo : FIFO inputs outputs nodes) → Ty
  | .input f | .output f | .advancing f | .initialized f => f.ty

structure VirtualRDA where
  inputs : List Ty
  outputs : List Ty
  numNodes : Nat
  nodes : NodeList numNodes
  fifos : List (FIFO inputs outputs nodes)

@[simp] def NodeOps.denote : NodeOps α β → (TysHList α → TysHList β)
  | .nop => id
  | .dropAll => λ _ => []
  | .add a b => λ inputs => ((inputs.get a) + (inputs.get b)) :: inputs
  | .mul a b => λ inputs => ((inputs.get a) * (inputs.get b)) :: inputs
  | .select _ a => λ inputs => inputs.get a :: []
  | .comp f g => g.denote ∘ f.denote

namespace Node

  def nextState (node : Node)
    (inputs : TysHList node.inputs)
    (currState : TysHList node.state)
      : TysHList node.state :=
    node.stateTransform.denote (currState ++ inputs)

  @[simp] def denote (node : Node)
    (inputs : TysHList node.inputs)
    (currState : TysHList node.state) : TysHList node.outputs :=
    node.pipeline.denote (currState ++ inputs)

end Node

namespace VirtualRDA

  def FIFOType (vrda : VirtualRDA) := FIFO vrda.inputs vrda.outputs vrda.nodes

  def isNodeInput (vrda : VirtualRDA) {nid : Fin vrda.numNodes} {ty : Ty}
    (port : Member ty (vrda.nodes.get nid).inputs) (fifo : vrda.FIFOType) : Bool :=
    match fifo with
      | .input fifo' | .initialized fifo' | .advancing fifo' =>
        if h : fifo'.consumer = nid ∧ fifo'.ty = ty then
          h.left ▸ h.right ▸ fifo'.consumerPort == port
        else
          false
      | _ => false

  def isGlobalOutput (vrda : VirtualRDA) {ty : Ty} (output : Member ty vrda.outputs)
    (fifo : vrda.FIFOType) : Bool :=
    match fifo with
      | .output fifo' =>
        if h : fifo'.ty = ty then
          h ▸ fifo'.consumer == output
        else
          false
      | _ => false

  def stateMap (vrda : VirtualRDA) :=
    (nid : Fin vrda.numNodes) → (TysHList (vrda.nodes.get nid).outputs) × (TysHList (vrda.nodes.get nid).state)

  def nthCycleState (vrda : VirtualRDA) (inputs : TysHListStream vrda.inputs) (n : Nat)
                      : vrda.stateMap :=
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

end VirtualRDA
