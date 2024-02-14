import Spacetalk.HList
import Spacetalk.Stream
import Mathlib.Data.Vector
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Logic.Basic
import Std.Data.List.Lemmas
import Mathlib.Tactic.Linarith

theorem List.mem_pwFilter {l : List α} {R : α → α → Prop} [DecidableRel R] {a : α} : a ∈ l.pwFilter R → a ∈ l := by
  intro h_mem
  -- How does the types work here with Set and List?
  apply Set.mem_of_subset_of_mem (List.pwFilter_subset l (R := R))
  exact h_mem

-- TODO: Simplify this proof
theorem List.mem_mergeSort {l : List α} {r : α → α → Prop} [DecidableRel r] {a : α} : a ∈ l.mergeSort r ↔ a ∈ l := by
  apply Iff.intro
  · intro h_mem
    apply Iff.mp
    apply List.Perm.mem_iff
    apply List.perm_mergeSort (r := r)
    exact h_mem
  · intro h_mem
    apply Iff.mpr
    apply List.Perm.mem_iff
    apply List.perm_mergeSort (r := r)
    exact h_mem


def finRangeRemovePair (n : Nat) (a b : Fin n) (h : a ≠ b) : Vector (Fin n) (n - 2) :=
  let v : Vector (Fin n) n := ⟨List.finRange n, List.length_finRange n⟩
  if h_lt : ↑b < ↑a then
    let v' := v.removeNth a
    v'.removeNth ⟨↑b, by
      apply Nat.lt_of_lt_of_le h_lt
      apply Nat.le_pred_of_lt
      exact a.is_lt
    ⟩
  else
    let v' := v.removeNth b
    v'.removeNth ⟨↑a, by
      apply Nat.lt_of_lt_of_le
      · apply Nat.lt_iff_le_and_ne.mpr
        apply And.intro
        · exact Nat.not_lt.mp h_lt
        · apply Fin.val_ne_iff.mpr h
      · apply Nat.le_pred_of_lt
        exact b.is_lt
    ⟩

namespace VirtualRDA

  -- Syntax

  inductive Ty
    | unit
    | nat
  deriving BEq, DecidableEq

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | nat => Nat

  instance {ty : Ty} : DecidableEq ty.denote :=
    λ a b =>
      match ty with
        | .unit => isTrue rfl
        | .nat => Nat.decEq a b

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

  -- More expressive adds that choose inputs with Fins
  -- monotonic to preserver old inputs
  inductive NodeOps : (inputs : List Ty) → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | dropAll : NodeOps α []
    | add : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
    | mul : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
    | select : (ty : Ty) → (a : Member ty inputs) → NodeOps inputs [ty]
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

  structure InputFIFO (inputs : List Ty) (numNodes : Nat) where
    ty : Ty
    producer : Member ty inputs
    consumer : Fin numNodes
    consumerPort: Nat
  deriving DecidableEq

  structure OutputFIFO (numNodes : Nat) where
    ty : Ty
    producer : Fin numNodes
    producerPort: Nat
  deriving DecidableEq

  structure AdvancingFIFO (numNodes : Nat) where
    ty : Ty
    producer : Fin numNodes
    consumer : Fin numNodes
    producerPort: Nat
    consumerPort: Nat
    adv : producer < consumer
  deriving DecidableEq

  structure InitializedFIFO (numNodes : Nat) where
    ty : Ty
    initialValue : ty.denote
    producer : Fin numNodes
    consumer : Fin numNodes
    producerPort: Nat
    consumerPort: Nat

  instance {nn : Nat} : DecidableEq (InitializedFIFO nn) :=
    λ a b => by
      rw [InitializedFIFO.mk.injEq]
      apply Decidable.byCases (p := a.ty = b.ty)
      · intro h_ty_eq
        have h_dety_eq : a.ty.denote = b.ty.denote := by rw [h_ty_eq]
        apply Decidable.byCases (p := cast h_dety_eq a.initialValue = b.initialValue)
        · intro h_init_eq
          apply Decidable.byCases (p := a.producer = b.producer ∧
                                        a.consumer = b.consumer ∧
                                        a.producerPort = b.producerPort ∧
                                        a.consumerPort = b.consumerPort)
          · intro h_rest_eq
            apply isTrue
            apply And.intro h_ty_eq
            apply And.intro
            · exact heq_of_cast_eq h_dety_eq h_init_eq
            · exact h_rest_eq
          · intro h_rest_neq
            apply isFalse
            intro h_eq
            apply h_rest_neq
            exact h_eq.right.right
        · intro h_init_neq
          apply isFalse
          intro h_and
          apply h_init_neq
          apply cast_eq_iff_heq.mpr
          exact h_and.right.left
      · intro h_ty_neq
        apply isFalse
        simp
        intro
        contradiction

  inductive FIFO (inputs : List Ty) (numNodes : Nat)
    | input : InputFIFO inputs numNodes → FIFO inputs numNodes
    | output : OutputFIFO numNodes → FIFO inputs numNodes
    | advancing : AdvancingFIFO numNodes → FIFO inputs numNodes
    | initialized : InitializedFIFO numNodes → FIFO inputs numNodes
  deriving DecidableEq

  namespace FIFO

    @[simp] def ty : FIFO inputs nn → Ty
      | .input fifo | .output fifo | .advancing fifo | .initialized fifo => fifo.ty

    @[simp] def isInput : FIFO inputs nn → Bool
      | .input _ => true
      | _ => false

    @[simp] def isOutput : FIFO inputs nn → Bool
      | .output _ => true
      | _ => false

    @[simp] def producer : (fifo : FIFO inputs nn) → fifo.isInput = false → Fin nn
      | .initialized fifo', _ | .advancing fifo', _ | .output fifo', _ => fifo'.producer

    def producerPort : (fifo : FIFO inputs nn) → fifo.isInput = false → Nat
      | .initialized fifo, _ | .advancing fifo, _ | .output fifo, _ => fifo.producerPort

    def consumerPort : (fifo : FIFO inputs nn) → fifo.isOutput = false → Nat
      | .input fifo, _ | .advancing fifo, _ | .initialized fifo, _ => fifo.consumerPort

  end FIFO

  def FIFOList (inputs : List Ty) (numNodes numFIFOs : Nat) :=
    {v : Vector (FIFO inputs numNodes) numFIFOs // List.Nodup v.toList}

  def FIFOList.get (fifos: FIFOList ins nn nf) (i : Fin nf) : FIFO ins nn :=
    fifos.val.get i

  namespace FIFOList

    @[simp] def ty (fifos : FIFOList ins nn nf) (i : Fin nf) :=
      (fifos.get i).ty

    @[simp] def isNodeInput (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
      match fifos.get i with
        | .input fifo | .advancing fifo | .initialized fifo => fifo.consumer == nid
        | _ => false

    @[simp] def isNodeOutput (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
      match fifos.get i with
        | .output fifo | .advancing fifo | .initialized fifo => fifo.producer == nid
        | _ => false

    def NonInputFid (fifos : FIFOList ins nn nf) :=
      {fid : Fin nf // (fifos.get fid).isInput = false}

    instance {fifos : FIFOList ins nn nf} : BEq fifos.NonInputFid where
      beq := λ a b => a.val = b.val

    instance {fifos : FIFOList ins nn nf} : DecidableEq fifos.NonInputFid :=
      λ a b => by
        apply Decidable.byCases (p := a.val = b.val)
        · intro h_eq
          apply isTrue
          apply Subtype.eq
          exact h_eq
        · intro h_neq
          apply isFalse
          intro h_eq
          apply h_neq
          apply Subtype.coe_inj.mpr
          exact h_eq

    instance {fifos : FIFOList ins nn nf} : LawfulBEq fifos.NonInputFid where
      eq_of_beq {a b} h := by
        apply Subtype.eq
        simp [BEq.beq] at h
        exact h
      rfl {a} := by simp [BEq.beq]

    instance {fifos : FIFOList ins nn nf} {fid : fifos.NonInputFid} : CoeDep fifos.NonInputFid fid (Fin nf) where
      coe := fid.val

    def NonOutputFid (fifos : FIFOList ins nn nf) :=
      {fid : Fin nf // (fifos.get fid).isOutput = false}

    instance {fifos : FIFOList ins nn nf} : BEq fifos.NonOutputFid where
      beq := λ a b => a.val = b.val

    instance {fifos : FIFOList ins nn nf} : DecidableEq fifos.NonOutputFid :=
      λ a b => by
        apply Decidable.byCases (p := a.val = b.val)
        · intro h_eq
          apply isTrue
          apply Subtype.eq
          exact h_eq
        · intro h_neq
          apply isFalse
          intro h_eq
          apply h_neq
          apply Subtype.coe_inj.mpr
          exact h_eq

    instance {fifos : FIFOList ins nn nf} : LawfulBEq fifos.NonOutputFid where
      eq_of_beq {a b} h := by
        apply Subtype.eq
        simp [BEq.beq] at h
        exact h
      rfl {a} := by simp [BEq.beq]

    instance {fifos : FIFOList ins nn nf} {fid : fifos.NonOutputFid} : CoeDep fifos.NonOutputFid fid (Fin nf) where
      coe := fid.val

    theorem filtered_input_is_not_output {fifos : FIFOList ins nn nf} {fid : Fin nf}
      (h_mem : fid ∈ (List.finRange nf).filter (fifos.isNodeInput nid))
      : (fifos.get fid).isOutput = false := by
      simp [List.mem_filter] at h_mem
      cases h_match : fifos.get fid <;> simp; simp [h_match] at h_mem

    def consumer_port_sort_rel {fifos : FIFOList ins nn nf} (a : fifos.NonOutputFid) (b : fifos.NonOutputFid) : Prop :=
      ((fifos.get a.val).consumerPort a.property) < ((fifos.get b.val).consumerPort b.property)

    instance {fifos : FIFOList ins nn nf} : DecidableRel fifos.consumer_port_sort_rel :=
      λ a b => by
        apply Nat.decLt

    @[simp] def NodeInputFids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List fifos.NonOutputFid :=
      let finRange := List.finRange nf
      let inputFids := finRange.filter (fifos.isNodeInput nid)
      let attached := inputFids.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, filtered_input_is_not_output h_mem⟩)
      let sorted := attached.mergeSort consumer_port_sort_rel
      sorted

    @[simp] def NodeInputTys (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
      let inputFids := fifos.NodeInputFids nid
      inputFids.map fifos.ty

    theorem filtered_output_is_not_input {fifos : FIFOList ins nn nf} {fid : Fin nf}
      (h_mem : fid ∈ (List.finRange nf).filter (fifos.isNodeOutput nid))
      : (fifos.get fid).isInput = false := by
      simp [List.mem_filter] at h_mem
      cases h_match : fifos.get fid <;> simp; simp [h_match] at h_mem

    def producer_port_sort_rel {fifos : FIFOList ins nn nf} (a : fifos.NonInputFid) (b : fifos.NonInputFid) : Prop :=
      ((fifos.get a.val).producerPort a.property) < ((fifos.get b.val).producerPort b.property)

    instance {fifos : FIFOList ins nn nf} : DecidableRel fifos.producer_port_sort_rel :=
      λ a b => by
        apply Nat.decLt

    def NodeOutputFidsPreSort (fifos : FIFOList ins nn nf) (nid : Fin nn) : List fifos.NonInputFid :=
      let finRange := List.finRange nf
      let outputFids := finRange.filter (fifos.isNodeOutput nid)
      let attached := outputFids.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, filtered_output_is_not_input h_mem⟩)
      attached

    theorem mem_NodeOutputFidsPreSort {fifos : FIFOList ins nn nf} {nid : Fin nn} {fid : fifos.NonInputFid}
      (h : fifos.get fid = fifo) (h_is_not_input : fifo.isInput = false)
      (h_prod : fifo.producer h_is_not_input = nid)
      : fid ∈ fifos.NodeOutputFidsPreSort nid := by
      simp only [FIFOList.NodeOutputFidsPreSort]
      apply List.mem_map.mpr
      exists ⟨fid, by
        apply List.mem_filter.mpr
        apply And.intro
        · simp
        · simp
          rw [h]
          cases h_match : fifo
          simp [h_match] at h_is_not_input
          all_goals simp_rw [h_match] at h_prod
          all_goals rw[←h_prod]
          all_goals simp
      ⟩
      apply And.intro
      · apply List.mem_attach
      · rfl

    @[simp] def NodeOutputFids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List fifos.NonInputFid :=
      let attached := fifos.NodeOutputFidsPreSort nid
      let sorted := attached.mergeSort (λ a b => fifos.producer_port_sort_rel a b)
      sorted

    @[simp] def NodeOutputTys (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
      let outputFids := fifos.NodeOutputFids nid
      outputFids.map (fifos.ty ∘ Subtype.val)

  end FIFOList

  structure Node (fifos : FIFOList inputs num_nodes num_fifos) (nid : Fin num_nodes) where
    state : List Ty
    initialState : TysHList state
    stateTransform : NodeOps (state ++ (fifos.NodeInputTys nid)) state
    pipeline : NodeOps (state ++ (fifos.NodeInputTys nid)) (fifos.NodeOutputTys nid)

  def NodeList (fifos : FIFOList inputs num_nodes num_fifos) :=
    (nid : Fin num_nodes) → Node fifos nid

  structure VirtualRDA where
    inputs : List Ty
    numNodes : Nat
    numFifos : Nat
    fifos : FIFOList inputs numNodes numFifos
    nodes : NodeList fifos

  -- Semantics

  @[simp] def NodeOps.denote : NodeOps α β → (TysHList α → TysHList β)
    | .nop => id
    | .dropAll => λ _ => []
    | .add a b => λ inputs => ((inputs.get a) + (inputs.get b)) :: inputs
    | .mul a b => λ inputs => ((inputs.get a) * (inputs.get b)) :: inputs
    | .select _ a => λ inputs => inputs.get a :: []
    | .comp f g => g.denote ∘ f.denote

  namespace Node

    def nextState (node : Node fifos nid)
      (inputs : TysHList (fifos.NodeInputTys nid))
      (currState : TysHList node.state)
       : TysHList node.state :=
      node.stateTransform.denote (currState ++ inputs)

    @[simp] def denote (node : Node fifos nid)
      (inputs : TysHList (fifos.NodeInputTys nid))
      (currState : TysHList node.state) : TysHList (fifos.NodeOutputTys nid) :=
      node.pipeline.denote (currState ++ inputs)

  end Node

  namespace VirtualRDA

    def stateMap (vrda : VirtualRDA) :=
      (nid : Fin vrda.numNodes) → (TysHList (vrda.fifos.NodeOutputTys nid)) × (TysHList (vrda.nodes nid).state)

    theorem filtered_output_is_not_input {vrda : VirtualRDA} {fid : Fin vrda.numFifos}
      (h_mem : fid ∈ (List.finRange vrda.numFifos).filter (λ i => (vrda.fifos.get i).isOutput))
      : (vrda.fifos.get fid).isInput = false := by
      simp [List.mem_filter] at h_mem
      cases h_match : vrda.fifos.get fid <;> simp; simp [h_match] at h_mem

    def outputFifos (vrda : VirtualRDA) : List vrda.fifos.NonInputFid :=
      let finRange := List.finRange vrda.numFifos
      let filtered := finRange.filter (λ i => (vrda.fifos.get i).isOutput)
      filtered.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, filtered_output_is_not_input h_mem⟩)

    theorem output_fid_idx_lt_output_tys_length {vrda : VirtualRDA} {fid : vrda.fifos.NonInputFid} {fifo : FIFO vrda.inputs vrda.numNodes}
      (h : vrda.fifos.get fid = fifo) (h_is_not_input : fifo.isInput = false)
      : (vrda.fifos.NodeOutputFids (fifo.producer h_is_not_input)).indexOf fid
        < (vrda.fifos.NodeOutputTys (fifo.producer h_is_not_input)).length := by
      have h_len_eq : (vrda.fifos.NodeOutputTys (fifo.producer h_is_not_input)).length = (vrda.fifos.NodeOutputFids (fifo.producer h_is_not_input)).length := by
        apply List.length_map
      rw [h_len_eq]
      simp only [List.indexOf]
      apply List.findIdx_lt_length_of_exists
      · exists fid
        apply And.intro
        · simp only [FIFOList.NodeOutputFids, FIFOList.NodeOutputFidsPreSort]
          apply List.mem_mergeSort (r := vrda.fifos.producer_port_sort_rel).mpr
          apply vrda.fifos.mem_NodeOutputFidsPreSort h h_is_not_input
          rfl
        · simp

    def extractOutput {vrda : VirtualRDA} {fid : vrda.fifos.NonInputFid} {fifo : FIFO vrda.inputs vrda.numNodes}
      (h : vrda.fifos.get fid = fifo) (h_is_not_input : fifo.isInput = false)
      (outputs : TysHList (vrda.fifos.NodeOutputTys (fifo.producer h_is_not_input))) : fifo.ty.denote :=

      let producerId := fifo.producer h_is_not_input
      let outputFids := vrda.fifos.NodeOutputFids producerId
      let outputTys := vrda.fifos.NodeOutputTys producerId

      let idx : Fin outputTys.length := ⟨outputFids.indexOf fid, output_fid_idx_lt_output_tys_length h h_is_not_input⟩
      let h_eq : Member (outputTys.get idx) outputTys = Member fifo.ty outputTys := by
        have : outputTys.get idx = fifo.ty := by
          simp_rw [←h]
        rw [this]
      let mem := h_eq ▸ (outputTys.nth_member idx)
      outputs.get mem

    theorem advancing_fifo_lt {vrda : VirtualRDA} {nid : Fin vrda.num_nodes} {fid : vrda.fifos.non_output_fid} {fifo : AdvancingFIFO vrda.num_nodes}
      (h_mem : fid ∈ vrda.fifos.NodeInputFids nid) (h_match : vrda.fifos fid.val = FIFO.advancing fifo)
      : fifo.producer < nid := by
      have h_is_input : vrda.fifos.is_node_input nid fid.val = true
      · simp at h_mem
        have h_mem' : fid.val ∈ (List.finRange vrda.num_fifos).filter (vrda.fifos.is_node_input nid)
        · have h_mem'' : fid ∈ (List.map
                                (λ ⟨fid, h_mem⟩ => ⟨fid, vrda.fifos.filtered_input_is_not_output h_mem⟩)
                                (List.attach (List.pwFilter (fun a b => fifos vrda a ≠ fifos vrda b) (List.filter (FIFOList.is_node_input vrda.fifos nid) (List.finRange vrda.num_fifos))))) := by
            apply List.mem_mergeSort (r := vrda.fifos.consumer_port_sort_rel)
            exact h_mem
          simp at h_mem''
          cases h_mem'' with
          | intro x px =>
            cases px with
              | intro y py =>
                have h_x_eq : fid.val = x
                · symm at py
                  rw [py]
                rw [h_x_eq]
                exact (List.mem_pwFilter y)
        exact (List.mem_filter.mp h_mem').right
      have h_consumer_eq : nid = fifo.consumer
      . simp [h_match] at h_is_input
        symm
        assumption
      rw [h_consumer_eq]
      exact fifo.adv

    def convert_fifo_ty {vrda : VirtualRDA} {coe : Idx → Fin vrda.num_fifos} {fid : Idx}
                      {fifo : FIFO vrda.inputs vrda.num_nodes} (h_match : vrda.fifos (coe fid) = fifo)
                      (val : fifo.get_ty.denote)
                      : (vrda.fifos.get_ty coe fid).denote :=
      let h_eq : fifo.get_ty = (vrda.fifos.get_ty coe) fid := by simp [h_match]
      h_eq ▸ val

    theorem input_map_attach_eq {vrda : VirtualRDA} {nid : Fin vrda.num_nodes}
      : vrda.fifos.NodeInputTys nid = ((vrda.fifos.NodeInputFids nid).attach.map (vrda.fifos.get_ty Subtype.val ∘ Subtype.val)) := by
      rw [List.comp_map (vrda.fifos.get_ty Subtype.val) Subtype.val]
      simp

    def nth_cycle_state (vrda : VirtualRDA) (inputs : TysHListStream vrda.inputs) (n : Nat)
                        : vrda.state_map :=
      λ nid =>
        let input_fids : List vrda.fifos.non_output_fid := vrda.fifos.NodeInputFids nid
        let input_vals : TysHList (vrda.fifos.NodeInputTys nid) :=
          input_map_attach_eq ▸ input_fids.attach.to_hlist (vrda.fifos.get_ty Subtype.val ∘ Subtype.val) (
            λ ⟨fid, h_mem⟩ =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .input fifo, _ =>
                  let val := (inputs n).get fifo.producer
                  convert_fifo_ty h_match val
                | .advancing fifo, _ =>
                  have := advancing_fifo_lt h_mem h_match
                  let producer_outputs := (vrda.nth_cycle_state inputs n fifo.producer).fst
                  let val := extract_fifo_output h_match rfl producer_outputs
                  convert_fifo_ty h_match val
                | .initialized fifo, _ =>
                  let val := match n with
                    | 0 => fifo.initial_value
                    | n' + 1 =>
                      let last_outputs := (vrda.nth_cycle_state inputs n' fifo.producer).fst
                      extract_fifo_output h_match rfl last_outputs
                  convert_fifo_ty h_match val
          )
        let node := vrda.nodes nid
        let outputs := node.denote input_vals node.initial_state
        let next_state := node.next_state input_vals node.initial_state
        (outputs, next_state)
        termination_by nth_cycle_state _ _ n nid => (n, nid)

    @[simp] def denote (vrda : VirtualRDA) (inputs : TyStreamsHList vrda.inputs)
                      : TyStreamsHList (vrda.output_fifos.map (vrda.fifos.get_ty Subtype.val)) :=
      let packed_inputs := inputs.pack
      let state_stream := vrda.nth_cycle_state packed_inputs
      let packed_output_stream : TysHListStream (vrda.output_fifos.map (vrda.fifos.get_ty Subtype.val)) :=
        λ n =>
          vrda.output_fifos.to_hlist (vrda.fifos.get_ty Subtype.val) (
            λ fid =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .output fifo, _ =>
                  let producer_outputs := ((state_stream n) fifo.producer).fst
                  let val := extract_fifo_output h_match rfl producer_outputs
                  convert_fifo_ty h_match val
          )
      packed_output_stream.unpack


  end VirtualRDA

    -- builder functions

  theorem congr_contrapositive {f : α → β} {a b : α} (h : f a ≠ f b) : a ≠ b := by
    intro h_eq
    apply h
    rw [h_eq]

  structure IOConnection (vrda : VirtualRDA) where
    ty : Ty
    initial_value : ty.denote
    in_fid : Fin vrda.num_fifos
    out_fid : Fin vrda.num_fifos
    in_fifo : InputFIFO vrda.inputs vrda.num_nodes
    out_fifo : OutputFIFO vrda.num_nodes
    h_in : (vrda.fifos in_fid) = FIFO.input in_fifo
    h_out : (vrda.fifos out_fid) = FIFO.output out_fifo

  namespace IOConnection

    theorem io_fifos_neq (ioc : IOConnection vrda) : ioc.in_fid ≠ ioc.out_fid := by
      have h_fifo_neq : vrda.fifos ioc.in_fid ≠ vrda.fifos ioc.out_fid := by
        rw [ioc.h_in, ioc.h_out]
        simp
      apply congr_contrapositive h_fifo_neq

  end IOConnection

  def make_backedge (vrda : VirtualRDA) (ioc : IOConnection vrda) : VirtualRDA :=
    let filtered := finRangeRemovePair vrda.num_fifos ioc.in_fid ioc.out_fid ioc.io_fifos_neq
    let newFIFO := FIFO.initialized {
      ty := ioc.ty,
      initial_value := ioc.initial_value,
      producer := ioc.out_fifo.producer,
      consumer := ioc.in_fifo.consumer,
      producer_port := ioc.out_fifo.producer_port,
      consumer_port := ioc.in_fifo.consumer_port
    }

    let fifos' : FIFOList vrda.inputs vrda.num_nodes (vrda.num_fifos - 1) :=
      λ ⟨idx, h_idx⟩ =>
        if h_lt : idx < (vrda.num_fifos - 2) then
          let idx' : Fin vrda.num_fifos := filtered.get ⟨idx, h_lt⟩
          vrda.fifos idx'
        else
          newFIFO

    let nodes' : NodeList fifos' :=
      λ nid =>
        let node := vrda.nodes nid
        have inputs_eq : vrda.fifos.NodeInputTys nid = fifos'.NodeInputTys nid := by
          sorry
        have outputs_eq : vrda.fifos.NodeOutputTys nid = fifos'.NodeOutputTys nid := by
          sorry
        {
          state := node.state,
          initial_state := node.initial_state,
          state_transform := inputs_eq ▸ node.state_transform,
          pipeline := inputs_eq ▸ outputs_eq ▸ node.pipeline
          : Node fifos' nid
        }

    { vrda with
      num_fifos := vrda.num_fifos - 1,
      fifos := fifos',
      nodes := nodes'
    }

end VirtualRDA
