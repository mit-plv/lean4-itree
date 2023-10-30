import Spacetalk.Stream

-- Source Lang
namespace Step

  ------------------ Syntax ------------------

  inductive Ty
    | nat
    | fn : Ty → Ty → Ty
    | stream : Ty → Ty
  infixr:35 " × " => Ty.prod
  infixr:25 " → " => Ty.fn

  @[reducible] def Ty.denote : Ty → Type
    | nat => Nat
    | fn α β => α.denote → β.denote
    | stream ty => Stream' ty.denote

  inductive BinOp : Ty → Ty → Ty → Type
    | add : BinOp .nat .nat .nat
    | mul : BinOp .nat .nat .nat

  -- Exprs operate on not streams
  -- Progs operate on streams and are always stream(s) → stream(s)
  -- This is so that a final program is always a function from stream(s) to stream(s)

  inductive Expr : Ty → Type
    | const : {ty : Ty} → ty.denote → Expr ty
    | binop : BinOp α β δ → Expr (α → β → δ)

  inductive Prog (rep : Ty → Type) : Ty → Type
    | var : rep ty → Prog rep ty
    | lam : (rep dom → Prog rep ran) → Prog rep (dom → ran)
    | app : Prog rep (dom → ran) → Prog rep dom → Prog rep ran
    | zip : Expr (α → β → δ) → Prog rep (.stream α → .stream β → .stream δ)
    | map : Expr (α → β) → Prog rep (.stream α → .stream β)
    | reduce : Expr (α → β → α) → Nat → α.denote → Prog rep (.stream β → .stream α)
    | comp : Prog rep (β → δ) → Prog rep (α → β) → Prog rep (α → δ)
  infixr:90 " ∘ " => Prog.comp

  ------------------ Semantics ------------------

  @[simp] def BinOp.denote : BinOp α β δ → (α.denote → β.denote → δ.denote)
    | add => HAdd.hAdd
    | mul => HMul.hMul

  @[simp] def Expr.denote : Expr ty → ty.denote
    | const val => val
    | binop op => op.denote

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
    #eval (dp n).get 0
    #eval (dp' n).get 0

    theorem dp_equiv : ∀n : Nat, (dot_prod n).denote = dot_prod' n := by
      simp [dot_prod']
  end Example

end Step