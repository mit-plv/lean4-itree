import Spacetalk.HList
import Spacetalk.Stream
import Mathlib.Data.Vector
import Mathlib.Data.List.Range
import Mathlib.Logic.Basic
import Std.Data.List.Lemmas

namespace VirtualRDA

  -- Syntax

  inductive Ty
    | unit
    | nat

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | nat => Nat

  abbrev TyStream (ty : Ty) := Stream' (ty.denote)

  abbrev TyStreamsHList (tys : List Ty) := HList TyStream tys

  abbrev TysHList (tys : List Ty) := HList Ty.denote tys

  abbrev TysHListStream (tys : List Ty) := Stream' (TysHList tys)

  def pack_hlist_stream (shl : TyStreamsHList tys) : TysHListStream tys :=
    match tys with
      | [] => λ _ => []
      | h::t =>
        λ n =>
          let h_elem : h.denote := (shl.get .head) n
          let tail_streams : TyStreamsHList t :=
            match shl with
              | _ :: rest => rest
          h_elem :: (pack_hlist_stream tail_streams) n

  def unpack_hlist_stream (s : TysHListStream tys) : TyStreamsHList tys :=
    match tys with
      | [] => []
      | h::t =>
        let h_stream : Stream' h.denote := λ n => (s n).get .head
        let t_stream : TysHListStream t := λ n =>
          match s n with
            | _ :: rest => rest
        h_stream :: unpack_hlist_stream t_stream

  -- More expressive adds that choose inputs with Fins
  -- monotonic to preserver old inputs
  inductive NodeOps : List Ty → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | add : NodeOps [.nat, .nat] [.nat]
    | dup : NodeOps [α] [α, α]
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

  structure InputFIFO (inputs : List Ty) where
    ty : Ty
    producer : Member ty inputs
    consumer : Fin num_nodes

  structure OutputFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes

  structure AdvancingFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes
    adv : producer < consumer

  structure InitializedFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes
    initial_value : ty.denote

  inductive FIFO (inputs : List Ty) (num_nodes : Nat)
    | input : InputFIFO inputs → FIFO inputs num_nodes
    | output : OutputFIFO num_nodes → FIFO inputs num_nodes
    | advancing : AdvancingFIFO num_nodes → FIFO inputs num_nodes
    | initialized : InitializedFIFO num_nodes → FIFO inputs num_nodes

  @[simp] def FIFO.get_ty : FIFO inputs nn → Ty
    | .input fifo | .output fifo | .advancing fifo | .initialized fifo => fifo.ty

  def FIFO.is_input : FIFO inputs nn → Bool
    | .input _ | .initialized _ | .advancing _ => true
    | .output _ => false

  def FIFO.is_not_input : FIFO inputs nn → Bool
    | .input _ => false
    | _ => true

  def FIFO.is_output : FIFO inputs nn → Bool
    | .input _ | .initialized _ | .advancing _ => false
    | .output _ => true

  def FIFO.producer : (fifo : FIFO inputs nn) → fifo.is_not_input → Fin nn
    | .initialized fifo', _ | .advancing fifo', _ | .output fifo', _ => fifo'.producer

  def FIFOList (inputs : List Ty) (num_nodes num_fifos : Nat) :=
    Fin num_fifos → FIFO inputs num_nodes

  @[simp] def FIFOList.get_ty (coe : Idx → Fin nf) (fifos : FIFOList ins nn nf) (i : Idx) :=
    (fifos (coe i)).get_ty

  def FIFOList.is_node_input (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
    match fifos i with
      | .input fifo | .advancing fifo | .initialized fifo => fifo.consumer == nid
      | _ => false

  def FIFOList.non_output_fid (fifos : FIFOList ins nn nf) :=
    {fid : Fin nf // (fifos fid).is_input = true}

  def FIFOList.non_input_fid (fifos : FIFOList ins nn nf) :=
    {fid : Fin nf // (fifos fid).is_output = true}

  def FIFOList.node_input_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List fifos.non_output_fid :=
    let fin_range := List.finRange nf
    let filtered := fin_range.filter (fifos.is_node_input nid)
    filtered.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, by
      have h_is_input : fifos.is_node_input nid fid = true
      · apply (List.mem_filter.mp h_mem).right
      simp [FIFOList.is_node_input] at h_is_input
      simp [FIFO.is_input]
      cases h : fifos fid <;> simp; simp [h] at h_is_input
    ⟩)

  def FIFOList.node_inputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
    (fifos.node_input_fids nid).map (fifos.get_ty (·.val))

  def FIFOList.is_node_output (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
    match fifos i with
      | .output fifo | .advancing fifo | .initialized fifo => fifo.producer == nid
      | _ => false

  def FIFOList.node_output_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List (Fin nf) :=
    let fin_range := List.finRange nf
    fin_range.filter (fifos.is_node_output nid)

  def FIFOList.node_outputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
    (fifos.node_output_fids nid).map (fifos.get_ty id)

  structure Node (fifos : FIFOList inputs num_nodes num_fifos) (nid : Fin num_nodes) where
    state : List Ty
    initial_state : TysHList state
    state_transform : NodeOps (state ++ (fifos.node_inputs nid)) state
    pipeline : NodeOps (state ++ (fifos.node_inputs nid)) (fifos.node_outputs nid)

  -- We want nodes to be sorted in reverse post order
  def NodeList (fifos : FIFOList inputs num_nodes num_fifos) :=
    (nid : Fin num_nodes) → Node fifos nid

  structure VirtualRDA where
    inputs : List Ty
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList inputs num_nodes num_fifos
    nodes : NodeList fifos

  def VirtualRDA.state_map (vrda : VirtualRDA) :=
    (nid : Fin vrda.num_nodes) → (TysHList (vrda.fifos.node_outputs nid)) × (TysHList (vrda.nodes nid).state)

  def VirtualRDA.output_fifos (vrda : VirtualRDA) : List vrda.fifos.non_input_fid :=
    let fin_range := List.finRange vrda.num_fifos
    let filtered := fin_range.filter (λ i => (vrda.fifos i).is_output)
    filtered.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, by
      have h_is_output : (vrda.fifos fid).is_output = true
      · apply (List.mem_filter.mp h_mem).right
      simp [FIFO.is_output] at h_is_output
      simp [FIFO.is_output]
      cases h : vrda.fifos fid <;> simp [h] at h_is_output; simp
    ⟩)

  -- Semantics

  @[simp] def NodeOps.denote : NodeOps α β → (TysHList α → TysHList β)
    | nop => id
    | add => λ (a :: b :: []) => (a + b) :: []
    | dup => λ (a :: []) => a :: a :: []
    | comp f g => g.denote ∘ f.denote

  namespace Node

    def next_state (node : Node fifos nid)
      (inputs : TysHList (fifos.node_inputs nid))
      (curr_state : TysHList node.state)
       : TysHList node.state :=
      node.state_transform.denote (curr_state ++ inputs)

    @[simp] def denote (node : Node fifos nid)
      (inputs : TysHList (fifos.node_inputs nid))
      (curr_state : TysHList node.state) : TysHList (fifos.node_outputs nid) :=
      node.pipeline.denote (curr_state ++ inputs)

  end Node

  namespace VirtualRDA

    def get_output (vrda : VirtualRDA) (fid : Fin vrda.num_fifos)
      {fifo : FIFO vrda.inputs vrda.num_nodes} (h : vrda.fifos fid = fifo)
      (h_is_not_input : fifo.is_not_input = true)
      (outputs : TysHList (vrda.fifos.node_outputs (fifo.producer h_is_not_input))) : fifo.get_ty.denote :=

      let output_fids := vrda.fifos.node_output_fids (fifo.producer h_is_not_input)
      let output_tys := vrda.fifos.node_outputs (fifo.producer h_is_not_input)
      let idx := output_fids.indexOf fid

      let idx_fin : Fin output_tys.length := ⟨
        idx, by
          simp [List.indexOf, FIFOList.node_outputs]
          apply List.findIdx_lt_length_of_exists
          · simp [FIFOList.node_output_fids]
            apply List.mem_filter.mpr
            apply And.intro
            · apply List.mem_finRange
            · simp [FIFOList.is_node_output, h]
              cases fifo <;> simp [FIFO.producer]; simp [FIFO.is_not_input] at h_is_not_input
      ⟩

      let h_eq : Member (output_tys.get idx_fin) output_tys = Member fifo.get_ty output_tys :=
        by
          simp [FIFOList.node_outputs, FIFOList.get_ty, FIFO.get_ty, h]

      let mem : Member fifo.get_ty output_tys := h_eq ▸ (output_tys.nth_member idx_fin)

      outputs.get mem

    theorem adv_fifo_lt {vrda : VirtualRDA} {nid : Fin vrda.num_nodes} {fid : vrda.fifos.non_output_fid} {fifo : AdvancingFIFO vrda.num_nodes}
                    (h_mem : fid ∈ vrda.fifos.node_input_fids nid) (h_match : vrda.fifos fid.val = FIFO.advancing fifo)
                    : fifo.producer < nid := by
      have h_is_input : vrda.fifos.is_node_input nid fid.val = true
      · simp [FIFOList.node_input_fids] at h_mem
        have h_mem' : fid.val ∈ (List.finRange vrda.num_fifos).filter (vrda.fifos.is_node_input nid)
        · cases h_mem with
          | intro x px =>
            cases px with
              | intro y py =>
                have h_x_eq : fid.val = x
                · symm at py
                  rw [py]
                rw [h_x_eq]
                exact y
        apply (List.mem_filter.mp h_mem').right
      have h_consumer_eq : nid = fifo.consumer
      . simp [FIFOList.is_node_input, h_match] at h_is_input
        symm
        assumption
      rw [h_consumer_eq]
      exact fifo.adv

    def convert_output {vrda : VirtualRDA} {coe : Idx → Fin vrda.num_fifos} {fid : Idx}
                      {fifo : FIFO vrda.inputs vrda.num_nodes} (h_match : vrda.fifos (coe fid) = fifo)
                      (val : fifo.get_ty.denote)
                      : (vrda.fifos.get_ty coe fid).denote :=
      let h_eq : fifo.get_ty = (vrda.fifos.get_ty coe) fid := by simp [h_match]
      h_eq ▸ val

    def nth_cycle_state (vrda : VirtualRDA) (inputs : TysHListStream vrda.inputs) (n : Nat)
                        : vrda.state_map :=
      λ nid =>
        let input_fids : List vrda.fifos.non_output_fid := vrda.fifos.node_input_fids nid
        let input_vals : TysHList (vrda.fifos.node_inputs nid) :=
          HList.from_list_with_mem input_fids (vrda.fifos.get_ty (·.val))
            (λ fid h_mem =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .input fifo, _ =>
                  let val := (inputs n).get fifo.producer
                  convert_output h_match val
                | .advancing fifo, _ =>
                  have := adv_fifo_lt h_mem h_match
                  let producer_outputs : TysHList (vrda.fifos.node_outputs fifo.producer) :=
                    (vrda.nth_cycle_state inputs n fifo.producer).fst
                  let val := vrda.get_output fid.val h_match (by simp [FIFO.is_not_input]) producer_outputs
                  convert_output h_match val
                | .initialized fifo, _ =>
                  let val := match n with
                    | 0 => fifo.initial_value
                    | n' + 1 =>
                      let last_outputs := (vrda.nth_cycle_state inputs n' fifo.producer).fst
                      vrda.get_output fid.val h_match (by simp [FIFO.is_not_input]) last_outputs
                  convert_output h_match val
            )
        let node := vrda.nodes nid
        let outputs := node.denote input_vals node.initial_state
        let next_state := node.next_state input_vals node.initial_state
        (outputs, next_state)
        termination_by nth_cycle_state _ _ n nid => (n, nid)

    @[simp] def denote (vrda : VirtualRDA) (inputs : TyStreamsHList vrda.inputs)
                      : TyStreamsHList (vrda.output_fifos.map (vrda.fifos.get_ty (·.val))) :=
      let packed_inputs := pack_hlist_stream inputs
      let state_stream := vrda.nth_cycle_state packed_inputs
      let packed_output_stream : TysHListStream (vrda.output_fifos.map (vrda.fifos.get_ty (·.val))) :=
        λ n =>
          let curr_state := state_stream n
          HList.from_list (vrda.fifos.get_ty (·.val)) (
            λ fid =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .output fifo, _ =>
                  let producer_outputs := (curr_state fifo.producer).fst
                  let val := vrda.get_output fid.val h_match (by simp [FIFO.is_not_input]) producer_outputs
                  convert_output h_match val
          ) vrda.output_fifos
      unpack_hlist_stream packed_output_stream

  end VirtualRDA

end VirtualRDA
