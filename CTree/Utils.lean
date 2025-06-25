import Mathlib.Data.Rel
import Mathlib.Data.Vector3
import Mathlib.Data.QPF.Univariate.Basic

theorem Rel.comp_self {r : Rel α α} [IsRefl α r] [IsTrans α r] : r.comp r = r := by
  funext x y
  simp only [Rel.comp]
  apply propext
  apply Iff.intro
  · intro h
    have ⟨z, ⟨h1, h2⟩⟩ := h
    exact IsTrans.trans _ _ _ h1 h2
  · intro h
    exists x
    exact And.intro (IsRefl.refl x) h

instance {r : Rel α α} [IsRefl α r] : IsRefl α (flip r) where
  refl a := by
    simp only [flip]
    exact IsRefl.refl a

instance {r : Rel α α} [IsTrans α r] : IsTrans α (flip r) where
  trans a b c := by
    intro h1 h2
    simp only [flip] at *
    exact IsTrans.trans _ _ _ h2 h1

theorem flip_eq [IsSymm _ r] : flip r = r := by
  funext x y
  simp only [flip, eq_iff_iff]
  apply Iff.intro <;> apply IsSymm.symm

theorem Or.elim4 {motive : Prop} (hor : P1 ∨ P2 ∨ P3 ∨ P4)
  (h1 : P1 → motive) (h2 : P2 → motive) (h3 : P3 → motive) (h4 : P4 → motive) : motive :=
  hor.elim3 h1 h2 (λ hor =>
    match hor with
    | .inl h => h3 h
    | .inr h => h4 h
  )

/- Vector3 utilities -/
def _fin0 [Fin2.IsLT 0 n] : ULift (Fin2 n) := .up (.ofNat' 0)

def _fin1 [Fin2.IsLT 1 n] : ULift (Fin2 n) := .up (.ofNat' 1)

def _fin1Const (v : α) :=
  λ (i : ULift (Fin2 1)) =>
    match i.down with | .ofNat' 0 => v

open Vector3 in
def _fin2Const (x y : α) :=
  λ (i : ULift (Fin2 2)) => [x, y] i.down

open Vector3 in
theorem _fin2Const_inj {x y x' y' : α} (h : _fin2Const.{u1, u2} x y = _fin2Const x' y') : x = x' ∧ y = y' := by
  apply And.intro
  · have := congr (a₁ := .up (.ofNat' 0)) h rfl
    simp [_fin2Const, Fin2.ofNat'] at this
    exact this
  · have := congr (a₁ := .up (.ofNat' 1)) h rfl
    simp [_fin2Const, Fin2.ofNat'] at this
    exact this

def _elim0 {α : Type u} (i : ULift (Fin2 0)) : α :=
  i.down.elim0 (C := λ _ => α)

theorem _elim0_eq_all : ∀ x : ULift (Fin2 0) → α, x = _elim0 :=
  λ x => funext λ z => @z.down.elim0 λ _ => x z = _elim0 z

theorem elim0_lift {P : Prop} (z : ULift (Fin2 0)) : P :=
  @z.down.elim0 λ _ => P

theorem _fin1Const_fin0 : _fin1Const (c _fin0) = c := by
  funext i
  match i with
  | .up (.ofNat' 0) =>
    simp only [_fin1Const, Fin2.ofNat', _fin0]

theorem _fin2Const_fin0_fin1 {α} {cs : ULift (Fin2 2) → α} : _fin2Const (cs _fin0) (cs _fin1) = cs := by
  funext i
  match i with
  | .up (.ofNat' 0) =>
    simp only [_fin1Const, Fin2.ofNat', _fin0]
    rfl
  | .up (.ofNat' 1) =>
    simp only [_fin1Const, Fin2.ofNat', _fin0]
    rfl

theorem _fin1Const_inj (h : _fin1Const x = _fin1Const y) : x = y := by
  have := congr (a₁ := _fin0) h rfl
  simp only [_fin1Const, _fin0, Fin2.ofNat'] at this
  exact this

/- PFunctor utilities -/
theorem PFunctor.M.map_dest {P : PFunctor.{u}} {f : P.M → P.M} {x : P.M}
  : P.map f x.dest = ⟨x.dest.fst, f ∘ x.dest.snd⟩ := by
  match x.dest with
  | ⟨fst, snd⟩ =>
    simp only [map]

theorem exists_and_eq {α : Type u} {β : α → Type v} {a : α} {b1 b2 : β a} {P : (a : α) → (b1 : β a) → (b2 : β a) → Prop}
  (h : P a b1 b2)
  : ∃ a' b1' b2', Sigma.mk a b1 = ⟨a', b1'⟩ ∧ Sigma.mk a b2 = ⟨a', b2'⟩ ∧ P a' b1' b2' := by
  exists a, b1, b2

theorem corec_inl_eq_id {P : PFunctor.{u}} {F : P.M ⊕ β → P (P.M ⊕ β)} {g : γ → P.M}
  : (∀ x, F (Sum.inl x) = P.map Sum.inl x.dest) → (((PFunctor.M.corec F) ∘ Sum.inl) ∘ g) = g := by
  intro hF
  funext i
  apply PFunctor.M.bisim (λ t1 t2 => ∃ t, t1 = (((PFunctor.M.corec F) ∘ Sum.inl) ∘ t) i ∧ t2 = t i)
  · intro x y h
    have ⟨t, h⟩ := h
    rw [h.left, h.right]
    match hm : (t i).dest with
    | ⟨fst, snd⟩ =>
      simp only [Function.comp_apply, PFunctor.M.corec_def, hF, hm, PFunctor.map, PFunctor.M.dest_mk]
      apply exists_and_eq
      intro ii
      exists λ _ => snd ii
      apply And.intro _ rfl
      simp only [Function.comp_apply, PFunctor.M.corec_def, PFunctor.map, hF]
  · exists g

/- Multiple coinductive constructor calls -/

-- Is this actually the id pfunctor?
-- Does id even make sense for pfunctors?
def IdF : PFunctor.{u} :=
  ⟨PUnit, λ _ => PUnit⟩

def PFunctor.pow (P : PFunctor.{max u v, v}) : Nat → PFunctor.{max u v, v}
| 0 => P
| n + 1 => PFunctor.comp P (P.pow n)

instance : Pow PFunctor Nat where
  pow P n := P.pow n

/-- The sum of two pfunctors -/
def SumF (P1 P2 : PFunctor) : PFunctor :=
  ⟨P1.A ⊕ P2.A, λ a => match a with | .inl a => P1.B a | .inr a => P2.B a⟩

def PFunctor.sumPow (P : PFunctor) : Nat → PFunctor.{max u v, v}
| 0 => P
| n + 1 => SumF (P ^ (n + 1)) (PFunctor.sumPow P n)
infixl:70 " ⊕^ " => PFunctor.sumPow

def SumF.inl {P1 P2 : PFunctor} (x : P1.M) : (SumF P1 P2).M  :=
  .corec (λ x =>
    let ⟨s, c⟩ := x.dest
    ⟨.inl s, λ sl => c sl⟩
  ) x

def SumF.inr {P1 P2 : PFunctor} (x : P2.M) : (SumF P1 P2).M  :=
  .corec (λ x =>
    let ⟨s, c⟩ := x.dest
    ⟨.inr s, λ sr => c sr⟩
  ) x

def SumF.case (x : (SumF P1 P2).M) : P1 (SumF P1 P2).M ⊕ P2 (SumF P1 P2).M :=
  match x.dest with
  | ⟨.inl sl, c⟩ => .inl ⟨sl, c⟩
  | ⟨.inr sr, c⟩ => .inr ⟨sr, c⟩

def SumF.destL (x : P1 (SumF P1 P2).M) : (SumF P1 P2).M :=
  .mk ⟨.inl x.fst, x.snd⟩

def SumF.destR (x : P2 (SumF P1 P2).M) : (SumF P1 P2).M :=
  .mk ⟨.inr x.fst, x.snd⟩

def PFunctor.fold {P : PFunctor} (x : P.M) : (n : Nat) → (P ⊕^ n).M
| 0 => x
| n + 1 =>
  let x' := P.fold x n
  SumF.inr x'

/-

P1 => P'
P2 => P'
------------
(SumF P1 P2) => P'

P => P'
---------
P.M → P'.M

P => P' := P P'.M → P'.M

P.comp P => P

-/

/-- constructor for composition -/
def PFunctor.comp.pmk (P₂ P₁ : PFunctor) {α : Type u} (x : P₂ (P₁ α)) : comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/-- universe polymorphic destructor for composition -/
def PFunctor.comp.pget {P₂ P₁ : PFunctor} {α : Type u} (x : comp P₂ P₁ α) : P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

def PFunctor.unfold1 {P : PFunctor} (x : (P ⊕^ 1).M) : P.M :=
  .corec (λ x =>
    match SumF.case x with
    | .inl x =>
      let ⟨a1, c1⟩ := PFunctor.comp.pget x
      ⟨a1, λ b1 =>
        let ⟨a2, c2⟩ := c1 b1
        .mk ⟨.inr a2, λ b2 => c2 b2⟩
      ⟩
    | .inr x =>
      x
  ) x

def PFunctor.M.corec2 {P : PFunctor} {α : Type u}
  (F : ∀ {X : Type u}, (α → X) → α → P.M ⊕ P (P X) ⊕ P X) (x : α) : P.M :=
  .corec (λ (a : P.M ⊕ P α ⊕ α) =>
    match a with
    | .inl y => P.map .inl y.dest
    | .inr (.inl ⟨s, c⟩) =>
      ⟨s, λ i => .inr <| .inr <| c i⟩
    | .inr (.inr y) =>
      let y := F id y
      match y with
      | .inl y => P.map .inl y.dest
      | .inr (.inl ⟨s, c⟩) =>
        ⟨s, λ i => .inr <| .inl <| c i⟩
      | .inr (.inr ⟨s, c⟩) => ⟨s, λ i => .inr <| .inr <| c i⟩
  ) (.inr <| .inr x)

inductive PFunctor.UpTo3 (P : PFunctor) (X : Type u)
| res (x : P.M)
| one (x : P X)
| two (x : P <| P X)
| three (x : P <| P <| P X)

def PFunctor.unfold2 {P : PFunctor} (x : (P ⊕^ 2).M) : P.M :=
  .corec (λ x =>
    match SumF.case x with
    | .inl x =>
      let x := PFunctor.comp.pget x
      let ⟨a1, c1⟩ := x
      ⟨a1, λ b1 =>
        let ⟨a2, c2⟩ := c1 b1
        .mk ⟨.inr <| .inl a2, λ b2 => c2 b2⟩
      ⟩
    | .inr x =>
      let ⟨a1, c1⟩ := x
      match a1 with
      | .inl a1 =>
        let ⟨a1, a2⟩ := a1
        ⟨a1, λ _ => .mk ⟨.inr <| .inl ⟨a1, a2⟩, λ b2 => c1 b2⟩⟩
      | .inr a1 =>
        ⟨a1, λ b1 => c1 b1⟩
  ) x
