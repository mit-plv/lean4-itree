import Mathlib.Data.Stream.Defs
import Mathlib.Data.Vector

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons
notation "[" "]" => HList.nil

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | _::as, .tail h => as.get h

def HList.append : HList β is1 → HList β is2 → HList β (is1 ++ is2)
  | [], l => l
  | (h :: s), t => h :: s.append t

infix:67 " ++ " => HList.append

-- Given a List α, a function f : α → β,
-- return a HList with indices of type β and values of β-indexed type γ
-- using the mapping function g : (a : α) → γ (f a).
def HList.from_list {α : Type v1} {β : Type v2} {δ : β → Type u}
                    (f : α → β) (g : (a : α) → δ (f a)) : 
                    (l : List α) → HList δ (l.map f)
  | [] => []
  | h :: t => g h :: HList.from_list f g t


-- Source Lang
namespace Spatium

  -- Syntax

  inductive Ty
    | nat
    | prod : Ty → Ty → Ty
    | fn : Ty → Ty → Ty
    | stream : Ty → Ty
  infixr:35 " × " => Ty.prod
  infixr:25 " → " => Ty.fn

  @[reducible] def Ty.denote : Ty → Type
    | nat => Nat
    | prod α β => α.denote × β.denote
    | fn α β => α.denote → β.denote
    | stream ty => Stream' ty.denote

  inductive BinOp : Ty → Ty → Ty → Type
    | add : BinOp .nat .nat .nat
    | mul : BinOp .nat .nat .nat

  -- Exprs operate on not streams
  -- Progs operate on streams and are always stream(s) → stream(s)
  -- This is so that a final program is always a function from stream(s) to stream(s)

  inductive Expr : Ty → Type
    | const : Nat → Expr .nat
    | binop : BinOp α β δ → Expr (α → β → δ)

  def a : Nat → Nat
    | _ => 0
  def b : Nat → Nat → Nat
    | _ => 0
  #check (b ∘ a : Nat → Nat → Nat)
  #check Function.comp

  -- Cannot encode filter on infinite streams
  -- Filters must be done "locally"
  inductive Prog (rep : Ty → Type) : Ty → Type
    | var : rep ty → Prog rep ty
    | lam : (rep dom → Prog rep ran) → Prog rep (dom → ran)
    | app : Prog rep (dom → ran) → Prog rep dom → Prog rep ran
    | zip : Expr (α → β → δ) → Prog rep (.stream α → .stream β → .stream δ)
    | map : Expr (α → β) → Prog rep (.stream α → .stream β)
    | reduce : Expr (α → β → α) → Nat → α.denote → Prog rep (.stream β → .stream α)
    | comp : Prog rep (β → δ) → Prog rep (α → β) → Prog rep (α → δ)
  infixr:90 " ∘ " => Prog.comp

  -- Semantics

  @[simp] def BinOp.denote : BinOp α β δ → (α.denote → β.denote → δ.denote)
    | add => HAdd.hAdd
    | mul => HMul.hMul

  @[simp] def Expr.denote : Expr ty → ty.denote
    | const n => n
    | binop op => op.denote

  def Stream'.reduce (f : α → β → α) (dim : Nat) (a : α) (s : Stream' β) : Stream' α :=
    λ n =>
      let s_forwarded := s.drop (dim * n)
      let reduction_list := s_forwarded.take dim
      reduction_list.foldl f a

  @[simp] def Prog.denote : Prog Ty.denote ty → ty.denote
    | var x => x
    | lam f => λ x => (f x).denote
    | app f a => f.denote a.denote
    | zip f => Stream'.zip f.denote
    | map f => Stream'.map f.denote
    | reduce f dim init => Stream'.reduce f.denote dim init
    | comp f g => Function.comp f.denote g.denote

  namespace Example
    -- A dot product of length n vectors
    def dot_prod (n : Nat) : Prog rep (.stream .nat → .stream .nat → .stream .nat) :=
      let multiply := .zip (.binop .mul)
      let reduction := .reduce (.binop .add) n 0
      .lam λ a => .lam λ b => .app reduction (.app (.app multiply (.var a)) (.var b))

    def dot_prod' (n : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
      Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

    def sa : Stream' Nat := id
    def sb : Stream' Nat := id

    def dp (n : Nat) := (dot_prod n).denote sa sb
    def dp' (n : Nat) := dot_prod' n sa sb
    def n := 10
    #eval (dp n).nth 0
    #eval (dp' n).nth 0

    theorem dp_equiv : ∀n : Nat, (dot_prod n).denote = dot_prod' n := by
      simp [dot_prod']
  end Example

end Spatium

namespace HIR

  inductive Ty
    | nat
  
  inductive NodeOps : List Ty → List Ty → Type
    | add : NodeOps [.nat, .nat] [.nat]
  

end HIR

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

  structure VirtFlowConfig where
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList num_nodes num_fifos 
    nodes : NodeList fifos

  -- Semantics

  @[simp] def NodeOps.denote : NodeOps α β → (TysHL α → TysHL β)
    | nop => id
    | add => λ (.cons a (.cons b .nil)) => (a + b) :: []
    | dup => λ (a :: []) => (.cons a (.cons a .nil))
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

  namespace VirtFlowConfig

    def find_graph_inputs (vfc : VirtFlowConfig) : List Ty :=
      let filtered := vfc.fifos.toList.filter (match ·.producer with | .inr _ => true | .inl _ => false)
      filtered.map (·.ty)

    def find_output_fifos (vfc : VirtFlowConfig) : List (FIFO vfc.num_nodes) :=
      vfc.fifos.toList.filter (match ·.consumer with | .inr _ => true | .inl _ => false)
  
    def nth_output (vfc : VirtFlowConfig) (input_stream : TysHLS vfc.find_graph_inputs) (n : Nat) :
      (fifo : FIFO vfc.num_nodes) → fifo.ty.denote :=
      sorry

    @[simp] def denote (vfc : VirtFlowConfig) :
      TysHLS vfc.find_graph_inputs → TysHLS (vfc.find_output_fifos.map (·.ty)) :=
      λ input_stream => λ n =>
        HList.from_list (·.ty) (vfc.nth_output input_stream n) vfc.find_output_fifos

  end VirtFlowConfig

end VirtFlow
