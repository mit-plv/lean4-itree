import Spacetalk.Graph

namespace SimpleDataflow

  inductive Prim
    | bitVec : Nat → Prim
  deriving DecidableEq

  inductive Ty
    | prim : Prim → Ty
    | option : Prim → Ty
  deriving DecidableEq

  @[reducible] def Prim.denote : Prim → Type
    | bitVec w => BitVec w

  def Prim.default : (p : Prim) → p.denote
    | bitVec _ => 0

  @[reducible] def Ty.denote : Ty → Type
    | prim p => p.denote
    | option p => Option p.denote

  def Ty.default : (ty : Ty) → ty.denote
    | .prim p => p.default
    | .option _ => none

  def Ty.denoteBEq : (ty : Ty) → (ty.denote → ty.denote → Bool)
    | .prim _ => λ a b => a = b
    | .option _ => λ a b =>
      match a, b with
        | .some aa, .some bb => aa == bb
        | .none, .none => true
        | _, _ => false

  def Ty.denoteDecEq : (ty : Ty) → DecidableEq ty.denote
    | .prim _ => inferInstance
    | .option _ => inferInstance

  instance {ty : Ty} : BEq ty.denote where
    beq := ty.denoteBEq

  instance {ty : Ty} : DecidableEq ty.denote :=
    ty.denoteDecEq

  instance {ty : Ty} : LawfulBEq ty.denote where
    eq_of_beq := by
      intro a b h
      induction ty with
      | prim _ => aesop
      | option _ =>
        cases a <;> cases b <;> repeat (first | contradiction | aesop)
        simp [BEq.beq, Ty.denoteBEq] at h
        simp [h]

    rfl := by
      intro a
      cases ty
      · simp
      · cases a
        · rfl
        · simp [BEq.beq, Ty.denoteBEq]

  instance : Denote Ty where
    denote := Ty.denote
    default := Ty.default

  abbrev BitVecTy (w : Nat) := Ty.prim (Prim.bitVec w)
  abbrev BoolTy := Ty.prim (Prim.bitVec 1)

  inductive BinaryOp : Ty → Ty → Ty → Type
    | add : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
    | mul : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
    | umod : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
    | eq : BinaryOp α α BoolTy

  def BinaryOp.eval : BinaryOp α β γ → (α.denote → β.denote → γ.denote)
    | add => BitVec.add
    | mul => BitVec.mul
    | umod => BitVec.umod
    | eq => λ a b => if a == b then ⟨1, by simp⟩ else ⟨0, by simp⟩

  inductive UnaryOp : Ty → Ty → Type
    | some : UnaryOp (.prim α) (.option α)

  def UnaryOp.eval : UnaryOp α β → (α.denote → β.denote)
    | some => Option.some

  inductive Pipeline : (inputs : List Ty) → (outputs : List Ty) → Type
    | const : {α : Ty} → α.denote → Pipeline [] [α]
    | id : {tys : List Ty} → Pipeline tys tys
    | unaryOp : {α β : Ty} → UnaryOp α β → Pipeline [α] [β]
    | binaryOp : {α β γ : Ty} → BinaryOp α β γ → Pipeline [α, β] [γ]
    | mux : {α : Ty} → Pipeline [BoolTy, α, α] [α]
    | comp : {α β γ : List Ty} → Pipeline β γ → Pipeline α β → Pipeline α γ
    | par : {α β γ δ : List Ty} → Pipeline α β → Pipeline γ δ → Pipeline (α ++ γ) (β ++ δ)
    | split : {α β γ δ φ ρ : List Ty}
              → Pipeline α β
              → Pipeline (φ ++ β) γ
              → Pipeline (β ++ ρ) δ
              → Pipeline (φ ++ α ++ ρ) (γ ++ δ)
    | swap : {α β : Ty} → Pipeline [α, β] [β, α]

  def Pipeline.eval : Pipeline α β → (DenoList α → DenoList β)
    | const a => λ _ => [a]ₕ
    | id => (·)
    | unaryOp op => λ ([a]ₕ) => [op.eval a]ₕ
    | binaryOp op => λ ([a, b]ₕ) => [op.eval a b]ₕ
    | mux => λ ([c, a, b]ₕ) =>
      have : DecidableEq (BitVecTy 1).denote := inferInstance
      if c = ⟨1, by simp⟩ then [a]ₕ else [b]ₕ
    | comp f g => f.eval ∘ g.eval
    | par f g => λ inputs => let (a, b) := inputs.split; (f.eval a) ++ₕ (g.eval b)
    | split f g h => λ inputs =>
      let (phiAlpha, rho) := inputs.split
      let (phi, alpha) := phiAlpha.split
      let beta := f.eval alpha
      let gamma := g.eval (phi ++ₕ beta)
      let delta := h.eval (beta ++ₕ rho)
      gamma ++ₕ delta
    | swap => λ ([a, b]ₕ) => [b, a]ₕ

  def Ops (inputs outputs state : List Ty) :=
    Pipeline (inputs ++ state) (outputs ++ state)

  instance : NodeOps Ops where
    eval := λ pipeline inputs state => (pipeline.eval (inputs ++ₕ state)).split

  def DataflowMachine := DataflowGraph Ty Ops

end SimpleDataflow
