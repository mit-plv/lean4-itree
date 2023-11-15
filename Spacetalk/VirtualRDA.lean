import Spacetalk.HList
import Spacetalk.Stream
import Mathlib.Data.Vector
import Mathlib.Data.List.Range
import Mathlib.Logic.Basic
import Std.Data.List.Lemmas

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
  -- FUTURE: Conditional dequeues and enqueues (is is really needed?)

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

  def FIFO.is_initialized : FIFO inputs num_nodes → Bool
    | .initialized _ => true
    | _ => false

  def FIFOList (inputs : List Ty) (num_nodes num_fifos : Nat) :=
    Fin num_fifos → FIFO inputs num_nodes

  def FIFOList.get_ty (fifos : FIFOList ins nn nf) (i : Fin nf) :=
    match fifos i with
      | .input fifo | .output fifo | .advancing fifo | .initialized fifo => fifo.ty

  def FIFOList.is_node_input (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
    match fifos i with
      | .input fifo | .advancing fifo | .initialized fifo => fifo.consumer == nid
      | _ => false

  def FIFOList.node_input_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List (Fin nf) :=
    let fin_range := List.finRange nf
    fin_range.filter (fifos.is_node_input nid)

  def FIFOList.node_inputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
    (fifos.node_input_fids nid).map fifos.get_ty

  def FIFOList.is_node_output (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
    match fifos i with
      | .output fifo | .advancing fifo | .initialized fifo => fifo.producer == nid
      | _ => false

  def FIFOList.node_output_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List (Fin nf) :=
    let fin_range := List.finRange nf
    fin_range.filter (fifos.is_node_output nid)

  def FIFOList.node_outputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
    (fifos.node_output_fids nid).map fifos.get_ty

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

  def VirtualRDA.output_fifos (vrda : VirtualRDA) : List (Fin vrda.num_fifos) :=
    let fin_range := List.finRange vrda.num_fifos
    fin_range.filter (λ i => match vrda.fifos i with | .output _ => true | _ => false)

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

  -- forward/backward edges should have different types, backward edges should have initial values
  -- combination logic should be run in an order that makes termination obvious
  namespace VirtualRDA

    -- def extract_output_stream (vrda : VirtualRDA) (fid : Fin vrda.num_fifos) (nid : Fin vrda.num_nodes)
    --                           (node_output_streams : TyStreamsHList (vrda.fifos.node_outputs nid))
    --                           (h_match_producer : (vrda.fifos fid).producer = .inl nid) :=
    --   let output_fids := vrda.fifos.node_output_fids nid
    --   let outputs := vrda.fifos.node_outputs nid
    --   let idx := output_fids.indexOf fid

    --   -- Prove that fid actually exists in the node's outputs
    --   let h_fid_fin_mem : fid ∈ (List.finRange vrda.num_fifos) := by apply List.mem_finRange
    --   let h_is_output : (vrda.fifos.is_node_output nid fid) = true := by simp [FIFOList.is_node_output, h_match_producer]
    --   let h_fid_filter_mem := List.mem_filter.mpr (And.intro h_fid_fin_mem h_is_output)
    --   let h_fid_outputs_mem : ∃ x, x ∈ output_fids ∧ fid == x :=
    --     by
    --       simp [FIFOList.node_output_fids, FIFOList.node_output_fids]
    --       exact h_fid_filter_mem
    --   let idx_fin : Fin outputs.length := ⟨
    --     idx,
    --     by
    --       simp [List.indexOf, FIFOList.node_outputs]
    --       exact List.findIdx_lt_length_of_exists h_fid_outputs_mem
    --   ⟩

    --   -- Prove that idx gives the desired output type
    --   let h_eq : Member (outputs.get idx_fin) outputs = Member (vrda.fifos fid).ty outputs :=
    --     by
    --       simp [FIFOList.node_outputs]; simp [FIFOList.get_ty]
    --   let mem : Member (vrda.fifos fid).ty outputs := h_eq ▸ (outputs.nth_member idx_fin)

    --   node_output_streams.get mem

    -- def get_output_stream (vrda : VirtualRDA)  (inputs : TyStreamsHList vrda.inputs)
    --                       (fid : Fin vrda.num_fifos) : TyStream (vrda.fifos fid).ty :=
    --   match h_match : (vrda.fifos fid).producer with
    --     | .inl nid =>
    --       let node := vrda.nodes nid
    --       let node_input_streams := HList.from_list vrda.fifos.get_ty (vrda.get_output_stream inputs) (vrda.fifos.node_input_fids nid)
    --       let node_output_streams := node.denote node_input_streams
    --       vrda.extract_output_stream fid nid node_output_streams h_match
    --     | .inr mem => inputs.get mem

    def get_output (vrda : VirtualRDA) (fid : Fin vrda.num_fifos)
      {fifo : AdvancingFIFO vrda.num_nodes} (h : vrda.fifos fid = FIFO.advancing fifo)
      (outputs : TysHList (vrda.fifos.node_outputs fifo.producer)) : fifo.ty.denote :=

      let output_fids := vrda.fifos.node_output_fids fifo.producer
      let output_tys := vrda.fifos.node_outputs fifo.producer
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
      ⟩

      let h_eq : Member (output_tys.get idx_fin) output_tys = Member fifo.ty output_tys :=
        by
          simp [FIFOList.node_outputs, FIFOList.get_ty, h]

      let mem : Member fifo.ty output_tys := h_eq ▸ (output_tys.nth_member idx_fin)

      outputs.get mem

    def first_cycle_state (vrda : VirtualRDA) (inputs : TysHListStream vrda.inputs) : vrda.state_map :=
      λ nid =>
        let input_fids := vrda.fifos.node_input_fids nid
        let input_vals : TysHList (vrda.fifos.node_inputs nid) :=
          HList.from_list_with_mem input_fids vrda.fifos.get_ty
            (λ fid h_mem =>
              match h_match : vrda.fifos fid with
                | .input fifo =>
                  let val := (inputs 0).get fifo.producer
                  let h_eq : fifo.ty.denote = (vrda.fifos.get_ty fid).denote:=
                    by simp [FIFOList.get_ty, h_match]
                  h_eq ▸ val
                | .initialized fifo =>
                  let val := fifo.initial_value
                  let h_eq : fifo.ty.denote = (vrda.fifos.get_ty fid).denote:=
                    by simp [FIFOList.get_ty, h_match]
                  h_eq ▸ val
                | .advancing fifo =>
                  let producer_outputs : TysHList (vrda.fifos.node_outputs fifo.producer) :=
                    (vrda.first_cycle_state inputs fifo.producer).fst
                  let val := vrda.get_output fid h_match producer_outputs
                  let h_eq : fifo.ty.denote = (vrda.fifos.get_ty fid).denote:=
                    by simp [FIFOList.get_ty, h_match]
                  h_eq ▸ val
                | _ =>
                  -- impossible
                  sorry
            )
        sorry
        decreasing_by
          simp_wf
          have h_is_output : vrda.fifos.is_node_input nid fid = true
          · apply (List.mem_filter.mp h_mem).right
          have h_consumer_eq : nid = fifo.consumer
          . simp [FIFOList.is_node_input, h_match] at h_is_output
            symm
            assumption
          rw [h_consumer_eq]
          exact fifo.adv

    @[simp] def denote (vrda : VirtualRDA) :
      TyStreamsHList vrda.inputs → TyStreamsHList (vrda.output_fifos.map vrda.fifos.get_ty) :=
      sorry
      -- λ inputs =>
      --   HList.from_list vrda.fifos.get_ty (vrda.get_output_stream inputs) vrda.output_fifos

  end VirtualRDA

end VirtualRDA
