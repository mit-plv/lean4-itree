
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
    | minus : Op (.nat × .nat) .nat
    | mult : Op (.nat × .nat) .nat

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
    | minus => λ (a, b) => a - b
    | mult => λ (a, b) => a * b

  @[simp] def Term.denote : Term ty → ty.denote
    | const x => x
    | op x => x.denote
    | range n => List.range n.denote
    | zip a b => List.zip a.denote b.denote
    | map f l => List.map f.denote l.denote

end Spatium

-- (Virtual) RDA Spec
-- What optimizations should we do at this level?
namespace VirtFlow

  -- Syntax

  inductive Ty
    | nat

  inductive NodeOps : List Ty → List Ty → Type
    | add : NodeOps [.nat, .nat] [.nat]
    | sub : NodeOps [.nat, .nat] [.nat]
    | mul : NodeOps [.nat, .nat] [.nat]
    | dup : NodeOps [.nat] [.nat, .nat]
    | cons : NodeOps α β → NodeOps β γ → NodeOps α γ

  structure Node where
    α : List Ty
    β : List Ty
    ops : NodeOps α β

  -- Buffer sizes will be modeled later
  structure FIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes

  structure VirtFlowConfig where
    nodes : Array Node
    fifos : List (FIFO nodes.size)

  -- Semantics

  @[reducible] def Ty.denote : Ty → Type
    | nat => Nat

end VirtFlow
