import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3
import Mathlib.Data.Rel

@[reducible]
def Function.exp {α : Sort u} (f : α → α) (n : Nat) : α → α :=
  match n with
  | 0 => id
  | n + 1 => f ∘ (Function.exp f n)

def SumF (P1 P2 : PFunctor.{u}) : PFunctor.{u} :=
  ⟨Sum P1.A P2.A, λ a => match a with | .inl a => P1.B a | .inr a => P2.B a⟩

def PFunctor.exp (P : PFunctor.{u}) : Nat → PFunctor.{u}
| 0 => P
| n + 1 => PFunctor.comp P (P.exp n)

def Pn (P : PFunctor.{u}) : Nat → PFunctor.{u}
| 0 => P
| n + 1 => SumF (P.exp (n + 1)) (Pn P n)
infixl:70 " ^ " => Pn

def SumF.inl {P1 P2 : PFunctor.{u}} : P1.M → (SumF P1 P2).M  := sorry

def SumF.inr {P1 P2 : PFunctor.{u}} : P2.M → (SumF P1 P2).M  := sorry

def SumF.case : (SumF P1 P2).M → P1 (SumF P1 P2).M ⊕ P2 (SumF P1 P2).M := sorry

def SumF.destL : P1 (SumF P1 P2).M → (SumF P1 P2).M := sorry

def SumF.destR : P2 (SumF P1 P2).M → (SumF P1 P2).M := sorry

def PFunctor.fold {P : PFunctor.{u}} (x : P.M) : (n : Nat) → (P ^ n).M
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

def PFunctor.unfold {P : PFunctor.{u}} : (n : Nat) → (x : (P ^ n).M) → P.M
| 0 => id
| 1 => λ x => by
  rw [Pn, PFunctor.exp] at x
  rw [Pn, PFunctor.exp] at x
  sorry
| n + 1 => λ x =>
  match SumF.case x with
  | .inl x =>
    sorry
  | .inr x => sorry--(.mk (P.unfold n x))

def corecN {P : PFunctor.{u}} {α : Type u} (n : Nat)
  (F : ∀ {X : Type u}, (α → X) → α → P.M ⊕ (P ^ n) X) (x : α) : P.M :=
  let y : (P ^ n).M := PFunctor.M.corec' (λ rec y =>
    match F rec y with
    | .inl y => .inl <| PFunctor.fold y n
    | .inr y => .inr y
  ) x
  PFunctor.unfold n y

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

/--
Coinductive Choice Tree defined with `PFunctor.M`.
```
coinductive CTree (ε : Type → Type) (ρ : Type)
  | ret (v : ρ)
  | tau (t : CTree ε ρ)
  | vis {α} (e : ε α) (k : α → CTree ε ρ)
  | zero
  | choice : CTree ε ρ → CTree ε ρ → CTree ε ρ
```
-/

inductive CTree.shape (ε : Type → Type) (ρ : Type) : Type 1
| ret (v : ρ)
| tau
| vis (α : Type) (e : ε α)
| zero
| choice

def CTree.children {ε : Type → Type} {ρ : Type} : CTree.shape ε ρ → Type 1
| .ret _ => ULift (Fin2 0)
| .tau => ULift (Fin2 1)
| .vis α _ => ULift α
| .zero => ULift (Fin2 0)
| .choice => ULift (Fin2 2)

def CTree.P (ε : Type → Type) (ρ : Type) : PFunctor.{1} := ⟨CTree.shape ε ρ, CTree.children⟩

def CTree (ε : Type → Type) (ρ : Type) := (CTree.P ε ρ).M

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

namespace CTree
  /- Utilities -/
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

  section
  variable {ε : Type → Type} {ρ : Type}

  def _elim0 {α : Type u} (i : ULift (Fin2 0)) : α :=
    i.down.elim0 (C := λ _ => α)

  theorem _elim0_eq_all : ∀ x : ULift (Fin2 0) → α, x = _elim0 :=
    λ x => funext λ z => @z.down.elim0 λ _ => x z = _elim0 z

  /- Functor Constructors -/
  section
  variable {X : Type u}

  def mk' (s : shape ε ρ) (c : children s → X) : P ε ρ X :=
    .mk s c

  @[simp]
  def ret' (v : ρ) : P ε ρ X :=
    .mk (.ret v) _elim0

  @[simp]
  def tau' (t : X) : P ε ρ X :=
    .mk .tau (_fin1Const t)

  @[simp]
  def vis' {α : Type} (e : ε α) (k : α → X) : P ε ρ X :=
    .mk (.vis α e) (k ·.down)

  @[simp]
  def zero' : P ε ρ X :=
    .mk .zero _elim0

  @[simp]
  def choice' (t1 t2 : X) : P ε ρ X :=
    .mk .choice (_fin2Const t1 t2)

  end

  /- Type Constructors -/
  @[simp]
  def mk (t : P ε ρ (CTree ε ρ)) : CTree ε ρ :=
    PFunctor.M.mk t

  @[match_pattern, simp]
  def ret (v : ρ) : CTree ε ρ :=
    .mk <| ret' v

  @[match_pattern, simp]
  def tau (t : CTree ε ρ) : CTree ε ρ :=
    .mk <| tau' t

  def tauN (n : Nat) (t : CTree ε ρ) : CTree ε ρ :=
    match n with
    | 0 => t
    | n + 1 => tau (tauN n t)

  @[match_pattern, simp]
  def vis {α : Type} (e : ε α) (k : α → CTree ε ρ) : CTree ε ρ :=
    .mk <| vis' e k

  @[match_pattern, simp]
  def zero : CTree ε ρ :=
    .mk zero'

  @[match_pattern, simp]
  def choice (t1 t2 : CTree ε ρ) : CTree ε ρ :=
    .mk <| choice' t1 t2
  infixr:70 " ⊕ " => CTree.choice

  def trigger {α : Type} (e : ε α) : CTree ε α :=
    vis e (λ x => ret x)

  theorem _fin1Const_inj (h : _fin1Const x = _fin1Const y) : x = y := by
    have := congr (a₁ := _fin0) h rfl
    simp only [_fin1Const, _fin0, Fin2.ofNat'] at this
    exact this

  theorem ret_inj (h : @ret ε ρ x = ret y) : x = y := by
    simp only [ret, mk, ret'] at h
    have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
    exact shape.ret.inj this

  theorem vis_inj_α {e1 : ε α1} {e2 : ε α2} (h : vis e1 k1 = vis e2 k2) : α1 = α2 := by
    simp only [vis, mk, vis'] at h
    have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
    exact (shape.vis.inj this).left

  theorem vis_inj (h : vis e1 k1 = vis e2 k2) : e1 = e2 ∧ k1 = k2 := by
    simp only [vis, mk, vis'] at h
    have := Sigma.mk.inj (PFunctor.M.mk_inj h)
    apply And.intro
    · exact eq_of_heq (shape.vis.inj this.left).right
    · have := eq_of_heq this.right
      funext x
      have := congr (a₁ := .up x) this rfl
      simp only at this
      exact this

  theorem tau_inj (h : tau t1 = tau t2) : t1 = t2 := by
    simp only [tau, mk, tau'] at h
    have := eq_of_heq (Sigma.mk.inj (PFunctor.M.mk_inj h)).right
    exact _fin1Const_inj this

  theorem choice_inj (h : choice t1 t2 = choice t1' t2') : t1 = t1' ∧ t2 = t2' := by
    simp only [choice, mk, choice'] at h
    have := eq_of_heq (Sigma.mk.inj (PFunctor.M.mk_inj h)).right
    exact _fin2Const_inj this

  /- Specialized utilitie functions from Mathlib -/
  abbrev dest : CTree ε ρ → P ε ρ (CTree ε ρ) := PFunctor.M.dest (F := P ε ρ)

  abbrev P.map (f : α → β) := PFunctor.map (P ε ρ) f

  abbrev corec {α : Type u} := PFunctor.M.corec (F := P ε ρ) (X := α)

  abbrev corecOn {α : Type u} := PFunctor.M.corecOn (F := P ε ρ) (X := α)

  abbrev corec₁ {α : Type 1} := PFunctor.M.corec₁ (P := P ε ρ) (α := α)

  abbrev corec' {α : Type 1} := PFunctor.M.corec' (P := P ε ρ) (α := α)

  /- Vector3 utilities -/
  theorem elim0_lift {P : Prop} (z : ULift (Fin2 0)) : P :=
    @z.down.elim0 λ _ => P

  theorem _fin1Const_fin0 : _fin1Const (c _fin0) = c := by
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin1Const, Fin2.ofNat', _fin0]

  theorem _fin2Const_fin0_fin1 : _fin2Const (cs _fin0) (cs _fin1) = cs := by
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin1Const, Fin2.ofNat', _fin0]
      rfl
    | .up (.ofNat' 1) =>
      simp only [_fin1Const, Fin2.ofNat', _fin0]
      rfl

  def matchOn {motive : Sort u} (x : CTree ε ρ)
    (ret : (v : ρ) → motive)
    (tau : (c : CTree ε ρ) → motive)
    (vis : {α : Type} → (e : ε α) → (k : α → CTree ε ρ) → motive)
    (zero : motive)
    (choice : (c1 c2 : CTree ε ρ) → motive)
    : motive :=
    match x.dest with
    | ⟨.ret v, _⟩ =>
      ret v
    | ⟨.tau, c⟩ =>
      tau (c _fin0)
    | ⟨.vis _ e, k⟩ =>
      vis e (k ∘ .up)
    | ⟨.zero, _⟩ =>
      zero
    | ⟨.choice, cs⟩ =>
      choice (cs _fin0) (cs _fin1)

  /-- Custom dependent match function for CTrees -/
  def dMatchOn {motive : CTree ε ρ → Sort u} (x : CTree ε ρ)
    (ret : (v : ρ) → x = ret v → motive x)
    (tau : (c : CTree ε ρ) → x = tau c → motive x)
    (vis : (α : Type) → (e : ε α) → (k : α → CTree ε ρ) → x = vis e k → motive x)
    (zero : x = zero → motive x)
    (choice : (c1 c2 : CTree ε ρ) → x = choice c1 c2 → motive x)
    : motive x :=
    match hm : x.dest with
    | ⟨.ret v, snd⟩ =>
      ret v (by
        rw [_elim0_eq_all snd] at hm
        simp only [CTree.ret, ret', mk]
        rw [←hm]
        simp only [PFunctor.M.mk_dest]
      )
    | ⟨.tau, c⟩ =>
      tau (c _fin0) (by
        simp only [CTree.tau, tau', mk, _fin1Const_fin0]
        rw [←hm]
        simp only [PFunctor.M.mk_dest]
      )
    | ⟨.vis α e, k⟩ =>
      vis α e (k ∘ .up) (by
        simp only [CTree.vis, vis', mk]
        have : (fun x => (k ∘ ULift.up) x.down) = k := by
          simp_all only [Function.comp_apply]
          rfl
        rw [this]
        rw [←hm]
        simp only [PFunctor.M.mk_dest]
      )
    | ⟨.zero, snd⟩ =>
      zero (by
        rw [_elim0_eq_all snd] at hm
        simp only [CTree.zero, zero', mk]
        rw [←hm]
        simp only [PFunctor.M.mk_dest]
      )
    | ⟨.choice, cs⟩ =>
      choice (cs _fin0) (cs _fin1) (by
        simp only [CTree.choice, choice', mk, _fin2Const_fin0_fin1]
        rw [←hm]
        simp only [PFunctor.M.mk_dest]
      )

  /- Destructor utilities -/
  theorem dest_ret : PFunctor.M.dest (F := P ε ρ) (ret v) = ⟨.ret v, _elim0⟩ :=
    rfl

  theorem dest_tau : PFunctor.M.dest (F := P ε ρ) (tau t) = ⟨.tau, _fin1Const t⟩ :=
    rfl

  theorem dest_vis : PFunctor.M.dest (F := P ε ρ) (vis e k) = ⟨.vis _ e, k ∘ ULift.down⟩ :=
    rfl

  theorem dest_zero : PFunctor.M.dest (F := P ε ρ) zero = ⟨.zero, _elim0⟩ :=
    rfl

  theorem dest_choice : PFunctor.M.dest (F := P ε ρ) (choice c1 c2) = ⟨.choice, _fin2Const c1 c2⟩ :=
    rfl

  /- Functor Instance -/
  def map (f : α → β) (t : CTree ε α) : CTree ε β :=
    corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| ret <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k ∘ .up)
      | ⟨.zero, _⟩ =>
        .inl zero
      | ⟨.choice, cts⟩ =>
        let t1 := rec <| cts _fin0
        let t2 := rec <| cts _fin1
        .inr <| choice' t1 t2
    ) t

  instance : Functor (CTree ε) where
    map := map

  /- Basic map lemmas -/
  theorem map_ret {ε : Type → Type} : map (ε := ε) f (ret v) = ret (f v) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    exact _elim0_eq_all _

  theorem map_tau {ε : Type → Type} {c : CTree ε ρ} : map f (tau c) = tau (map f c) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', tau,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin1Const, Fin2.ofNat', Function.comp_apply, PFunctor.M.corec_def]
      rfl

  theorem map_vis {ε : Type → Type} {α : Type} {e : ε α} {k : α → CTree ε ρ} {f : ρ → σ}
    : map f (vis e k) = vis e (λ x => map f <| k x) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', vis,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    simp only [Function.comp_apply, PFunctor.M.corec_def]

  theorem map_zero {ε} {f : α → β} : map (ε := ε) f zero = zero := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    exact _elim0_eq_all _

  theorem map_choice {f : α → β} : map f (choice c1 c2) = choice (map f c1) (map f c2) := by
    simp only [map, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, ret, mk, ret',
      tau', Function.comp_apply, id_eq, vis', Function.id_comp, zero, zero', choice', choice,
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_eq]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin2Const, Nat.reduceAdd, Fin2.ofNat', Function.comp_apply, Vector3.cons_fz,
        PFunctor.M.corec_def]
      rfl
    | .up (.ofNat' 1) =>
      simp only [_fin2Const, Nat.reduceAdd, Fin2.ofNat', Function.comp_apply, Vector3.cons_fz,
        PFunctor.M.corec_def]
      rfl

  /- Monad Instance -/
  def bind {σ} (t : CTree ε ρ) (f : ρ → CTree ε σ) : CTree ε σ :=
    corec' (λ rec t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        .inl <| f v
      | ⟨.tau, c⟩ =>
        .inr <| tau' <| rec <| c _fin0
      | ⟨.vis _ e, k⟩ =>
        .inr <| vis' e (rec ∘ k ∘ .up)
      | ⟨.zero, _⟩ =>
        .inl zero
      | ⟨.choice, cts⟩ =>
        let t1 := rec <| cts _fin0
        let t2 := rec <| cts _fin1
        .inr <| choice' t1 t2
    ) t

  instance : Monad (CTree ε) where
    pure := ret
    bind := bind

  theorem bind_map (f : CTree ε (α → β)) (x : CTree ε α) : (f >>= λ f => map f x) = f <*> x := by
    simp only [Bind.bind, Seq.seq, Functor.map]

  /- Bind lemmas -/
  theorem bind_ret : bind (ret v) f = f v := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', ret, ret',
      PFunctor.M.corec_def, PFunctor.M.dest_mk, PFunctor.map_map]
    rw [PFunctor.M.map_dest]
    conv =>
      rhs
      rw [←PFunctor.M.mk_dest (x := f v)]
    match hm : PFunctor.M.dest (f v) with
    | ⟨fst, snd⟩ =>
      congr
      apply corec_inl_eq_id
      simp only [implies_true]

  theorem bind_tau : bind (tau c) f = tau (bind c f) := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      tau, PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [Function.comp_apply, PFunctor.M.corec_def]
      rfl

  theorem bind_vis : bind (vis e k) f = vis e λ x => bind (k x) f := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      vis, PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    funext i
    simp only [Function.comp_apply, PFunctor.M.corec_def]
    rfl

  theorem bind_zero : bind zero f = zero := by
    simp only [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, Bind.bind, Sum.bind, tau',
      Function.comp_apply, id_eq, vis', Function.id_comp, zero, mk, zero', choice', PFunctor.map,
      PFunctor.M.corec_def, PFunctor.M.dest_mk]
    congr
    exact _elim0_eq_all _

  theorem bind_choice : bind (choice c1 c2) f = choice (bind c1 f) (bind c2 f) := by
    simp [bind, corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def, PFunctor.map, Bind.bind, Sum.bind]
    congr
    funext i
    match i with
    | .up (.ofNat' 0) =>
      simp only [_fin0, _fin2Const, Nat.reduceAdd, Function.comp_apply, PFunctor.M.corec_def]
      rfl
    | .up (.ofNat' 1) =>
      simp only [_fin0, _fin2Const, Nat.reduceAdd, Function.comp_apply, PFunctor.M.corec_def]
      rfl

  /- Functor Laws -/

  /--
    `ctree_eq R t` tries to prove the equivalence of two `CTree`s transformed by `map` and `bind`.

    `R` should be of the form `λ t1 t2 => ∃ t, t1 = f t ∧ t2 = g t` where `f` and `g` are some function from `CTree` to `CTree` potentially involving `map` and `bind`.

    `t` is the initial value passed to the existential in `R`.
  -/
  macro "ctree_eq" " (" R:term ") " t:term : tactic => `(tactic|(
    apply PFunctor.M.bisim $R _
    · exists $t
    · intro x y h
      obtain ⟨t, h⟩ := h
      rw [h.left, h.right]
      apply dMatchOn t
      · intro v h
        simp only [h, map_ret, bind_ret, dest_ret, id]
        apply exists_and_eq
        intro i
        exact elim0_lift i
      · intro c h
        simp only [h, map_tau, bind_tau, dest_tau]
        apply exists_and_eq
        intro i
        exists c
        match i with
        | .up (.ofNat' 0) =>
          apply And.intro <;> simp only [_fin1Const, Fin2.ofNat']
      · intro α e k h
        simp only [h, map_vis, bind_vis, dest_vis]
        apply exists_and_eq
        intro i
        exists (k ∘ ULift.down) i
      · intro h
        simp only [h, map_zero, bind_zero, dest_zero]
        apply exists_and_eq
        intro i
        exact elim0_lift i
      · intro c1 c2 h
        simp only [h, map_choice, bind_choice, dest_choice]
        apply exists_and_eq
        intro i
        match i with
        | .up (.ofNat' 0) =>
          exists c1
        | .up (.ofNat' 1) =>
          exists c2
  ))

  theorem id_map (t : CTree ε ρ) : map id t = t := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map id t ∧ t2 = t) t

  theorem comp_map (g : α → β) (h : β → γ) (t : CTree ε α) : map (h ∘ g) t = map h (map g t) := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (h ∘ g) t ∧ t2 = map h (map g t)) t

  instance : LawfulFunctor (CTree ε) where
    map_const := by simp only [Functor.mapConst, Functor.map, implies_true]
    id_map := id_map
    comp_map := comp_map

  /- Monad Laws -/

  theorem map_const_left : map (Function.const α v) t = bind t λ _ => ret v := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (Function.const α v) t ∧ t2 = t.bind λ _ => ret v) t

  theorem map_const_right : map (Function.const α id v) t = t := by
    ctree_eq (λ t1 t2 => ∃ t, t1 = map (Function.const α id v) t ∧ t2 = t) t

  /--
    `ctree_eq_map_const R t` tries to prove the equivalence of two `CTree`s transformed by `seq` and `map` with `Function.const`.

    `R` should be of the form `λ t1 t2 => t1 = t2 ∨ ∃ x y, t1 = f x y ∧ t2 = g x y`.

    `x` and `y` are the initial values passed to the existential in `R`.
  -/
  macro "ctree_eq_map_const" " (" R:term ") " x:term ", " y:term : tactic => `(tactic|(
    apply PFunctor.M.bisim $R _
    · apply Or.inr
      exists $x, $y
    · intro x y h
      match h with
      | .inl h =>
        match hm : x.dest with
        | ⟨a, f⟩ =>
          exists a, f, f
          apply And.intro rfl
          apply And.intro _ λ _ => .inl rfl
          rw [←hm, h]
      | .inr ⟨x, y, h⟩ =>
        rw [h.left, h.right]
        simp only [SeqLeft.seqLeft, SeqRight.seqRight, Seq.seq, Functor.map]
        apply dMatchOn x
        · intro v h
          simp only [h, bind_ret, map_ret, map_const_left, map_const_right]
          apply exists_and_eq
          intro i
          exact Or.inl rfl
        · intro c h
          simp only [h, bind_tau, map_tau]
          simp only [tau, mk, tau', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c, y
        · intro _ e k h
          simp only [h, bind_vis, map_vis]
          simp only [vis, mk, vis']
          apply exists_and_eq
          intro i
          apply Or.inr
          exists k i.down, y
        · intro h
          simp only [h, bind_zero, map_zero]
          simp only [zero, mk, zero', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          exact elim0_lift i
        · intro c1 c2 h
          simp only [h, bind_choice, map_choice]
          simp only [choice, mk, choice', PFunctor.M.dest_mk]
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c1, y
          | .up (.ofNat' 1) =>
            exists c2, y
  ))

  theorem seqLeft_eq (x : CTree ε α) (y : CTree ε β) : x <* y = Function.const β <$> x <*> y := by
    ctree_eq_map_const (λ t1 t2 => (t1 = t2) ∨ ∃ (x : CTree ε α) (y : CTree ε β), (t1 = x <* y ∧ t2 = (Function.const β <$> x <*> y))) x, y

  theorem seqRight_eq (x : CTree ε α) (y : CTree ε β) : x *> y = Function.const α id <$> x <*> y := by
    ctree_eq_map_const (λ t1 t2 => t1 = t2 ∨ ∃ (x : CTree ε α) (y : CTree ε β), t1 = x *> y ∧ t2 = Function.const α id <$> x <*> y) x, y

  theorem pure_seq (g : α → β) (x : CTree ε α) : pure g <*> x = g <$> x := by
    simp only [Seq.seq, pure, bind_ret]

  theorem bind_pure_comp (f : α → β) (x : CTree ε α) : bind x (pure ∘ f) = map f x := by
    ctree_eq (λ t1 t2 => ∃ x, t1 = bind x (pure ∘ f) ∧ t2 = map f x) x

  theorem pure_bind (x : α) (f : α → CTree ε β) : bind (pure x) f = f x := by
    simp only [pure, bind_ret]

  theorem bind_assoc (x : CTree ε α) (f : α → CTree ε β) (g : β → CTree ε γ)
    : bind (bind x f) g = bind x λ x => bind (f x) g := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = t2 ∨ ∃ x, t1 = bind (bind x f) g ∧ t2 = bind x λ x => bind (f x) g) _
    · apply Or.inr
      exists x
    · intro x y h
      match h with
      | .inl h =>
        match hm : PFunctor.M.dest x with
        | ⟨a, f⟩ =>
          exists a, f, f
          apply And.intro rfl
          apply And.intro _ λ _ => Or.inl rfl
          rw [←hm, h]
      | .inr ⟨x, h⟩ =>
        rw [h.left, h.right]
        apply dMatchOn x
        · intro v h
          simp only [h, bind_ret, map_ret]
          match hm : PFunctor.M.dest (bind (f v) g) with
          | ⟨a, f⟩ =>
            exists a, f, f
            repeat apply And.intro rfl
            intro
            exact Or.inl rfl
        · intro c h
          simp only [h, bind_tau, map_tau]
          simp only [tau, mk, tau']
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c
        · intro _ e k h
          simp only [h, bind_vis, map_vis]
          simp only [vis, mk, vis']
          apply exists_and_eq
          intro i
          apply Or.inr
          exists k i.down
        · intro h
          simp only [h, bind_zero, map_zero]
          simp only [zero, mk, zero']
          apply exists_and_eq
          intro i
          exact elim0_lift i
        · intro c1 c2 h
          simp only [h, bind_choice, map_choice]
          simp only [choice, mk, choice']
          apply exists_and_eq
          intro i
          apply Or.inr
          match i with
          | .up (.ofNat' 0) =>
            exists c1
          | .up (.ofNat' 1) =>
            exists c2

  instance : LawfulMonad (CTree ε) where
    seqLeft_eq := seqLeft_eq
    seqRight_eq := seqRight_eq
    pure_seq := pure_seq
    bind_pure_comp := bind_pure_comp
    bind_map := bind_map
    pure_bind := pure_bind
    bind_assoc := bind_assoc

  macro "ctree_elim " h:term : tactic => `(tactic| try (have := (Sigma.mk.inj (PFunctor.M.mk_inj $h)).left; contradiction))

  /- Refinement -/

  inductive RefineF (r : Rel ρ σ) (sim : CTree ε ρ → CTree ε σ → Prop) : CTree ε ρ → CTree ε σ → Prop
  | ret (h : r x y) : RefineF r sim (ret x) (ret y)
  | vis {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
        (h : ∀ a : α, sim (k1 a) (k2 a)) : RefineF r sim (vis e k1) (vis e k2)
  | tau (h : sim t1 t2) : RefineF r sim t1.tau t2.tau
  | tau_left (h : RefineF r sim t1 t2) : RefineF r sim t1.tau t2
  | tau_right (h : RefineF r sim t1 t2) : RefineF r sim t1 t2.tau
  | zero {t : CTree ε σ} : RefineF r sim zero t
  | choice_left (h : sim t1 t2) : RefineF r sim t1 (t2 ⊕ t3)
  | choice_right (h : sim t1 t3) : RefineF r sim t1 (t2 ⊕ t3)
  | choice_idemp (h1 : sim t1 t3) (h2 : sim t2 t3) : RefineF r sim (t1 ⊕ t2) t3

  theorem RefineF.tauN_left (h : RefineF r sim t1 t2) : ∀ n, RefineF r sim (tauN n t1) t2 := by
    intro n
    induction n with
    | zero =>
      simp only [tauN]
      exact h
    | succ _ ih =>
      simp only [tauN]
      apply RefineF.tau_left
      exact ih

  theorem RefineF.tauN_right (h : RefineF r sim t1 t2) : ∀ n, RefineF r sim t1 (tauN n t2) := by
    intro n
    induction n with
    | zero =>
      simp only [tauN]
      exact h
    | succ _ ih =>
      simp only [tauN]
      apply RefineF.tau_right
      exact ih

  def Refine (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
  RefineF r (Refine r) t1 t2
  greatest_fixpoint monotonicity by
    intro _ _ hsim _ _ h
    induction h with
    | ret h => exact .ret h
    | vis h => exact .vis λ a => hsim _ _ <| h a
    | tau h => exact .tau (hsim _ _ h)
    | tau_left _ ih => exact RefineF.tau_left ih
    | tau_right _ ih => exact RefineF.tau_right ih
    | zero => exact .zero
    | choice_left h => exact .choice_left (hsim _ _ h)
    | choice_right h => exact .choice_right (hsim _ _ h)
    | choice_idemp h1 h2 => exact .choice_idemp (hsim _ _ h1) (hsim _ _ h2)

  -- `t1 r⊑ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ⊑"r:61"⊑ " t2:61 => Refine r t1 t2

  theorem Refine.coind (sim : CTree ε ρ → CTree ε σ → Prop) (adm : ∀ t1 t2, sim t1 t2 → RefineF r sim t1 t2)
    {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim t1 t2) : t1 ⊑r⊑ t2 :=
    Refine.fixpoint_induct r sim adm _ _ h

  -- Various custom destructors for instances of `Refine` and `RefineF`

  lemma RefineF.dest_tau_left_compat (h : RefineF r (Refine r) t1 t2) : RefineF r (λ t1 t2 => t1.tau ⊑r⊑ t2) t1 t2 := by
    induction h
    case tau h =>
      apply RefineF.tau
      rw [Refine] at *
      apply RefineF.tau_left
      exact h
    case tau_left _ ih =>
      apply RefineF.tau_left
      exact ih
    case tau_right _ ih =>
      apply RefineF.tau_right
      exact ih
    case choice_left h =>
      apply RefineF.choice_left
      rw [Refine] at *
      apply RefineF.tau_left
      exact h
    case choice_right h =>
      apply RefineF.choice_right
      rw [Refine] at *
      apply RefineF.tau_left
      exact h
    case choice_idemp h1 h2 =>
      apply RefineF.choice_idemp
      <;> (rw [Refine] at *; apply RefineF.tau_left)
      · exact h1
      · exact h2
    case zero =>
      exact RefineF.zero
    case ret h =>
      exact RefineF.ret h
    case vis h =>
      apply RefineF.vis
      intro a
      have := h a
      rw [Refine] at *
      apply RefineF.tau_left
      exact this

  theorem Refine.dest_tau_left (h : t1.tau ⊑r⊑ t2) : t1 ⊑r⊑ t2 := by
    apply Refine.coind (λ t1 t2 => t1.tau ⊑r⊑ t2) _ h
    intro t1 t2 h
    generalize ht1 : t1.tau = t1t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case tau h =>
      apply RefineF.tau_right
      rw [Refine] at *
      rw [tau_inj ht1]
      exact h.dest_tau_left_compat
    case tau_left h _ =>
      rw [tau_inj ht1]
      exact h.dest_tau_left_compat
    case tau_right ih =>
      apply RefineF.tau_right
      exact ih ht1
    case choice_left h =>
      apply RefineF.choice_left
      rw [ht1]
      exact h
    case choice_right h =>
      apply RefineF.choice_right
      rw [ht1]
      exact h

  theorem RefineF.dest_tau_left (h : RefineF r (Refine r) t1.tau t2) : RefineF r (Refine r) t1 t2 := by
    have := Refine.dest_tau_left (by rw [Refine]; exact h)
    rw [Refine] at this
    exact this

  lemma RefineF.dest_tau_right_compat (h : RefineF r (Refine r) t1 t2) : RefineF r (λ t1 t2 => t1 ⊑r⊑ t2.tau) t1 t2 := by
    induction h
    case tau h =>
      apply RefineF.tau
      rw [Refine] at *
      apply RefineF.tau_right
      exact h
    case tau_left _ ih =>
      apply RefineF.tau_left
      exact ih
    case tau_right _ ih =>
      apply RefineF.tau_right
      exact ih
    case choice_left h =>
      apply RefineF.choice_left
      rw [Refine] at *
      apply RefineF.tau_right
      exact h
    case choice_right h =>
      apply RefineF.choice_right
      rw [Refine] at *
      apply RefineF.tau_right
      exact h
    case choice_idemp h1 h2 =>
      apply RefineF.choice_idemp
      <;> (rw [Refine] at *; apply RefineF.tau_right)
      · exact h1
      · exact h2
    case zero =>
      exact RefineF.zero
    case ret h =>
      exact RefineF.ret h
    case vis h =>
      apply RefineF.vis
      intro a
      have := h a
      rw [Refine] at *
      apply RefineF.tau_right
      exact this

  theorem Refine.dest_tau_right (h : t1 ⊑r⊑ t2.tau) : t1 ⊑r⊑ t2 := by
    apply Refine.coind (λ t1 t2 => t1 ⊑r⊑ t2.tau) _ h
    intro t1 t2 h
    generalize ht2 : t2.tau = t2t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case tau h =>
      apply RefineF.tau_left
      rw [Refine] at *
      rw [tau_inj ht2]
      exact h.dest_tau_right_compat
    case tau_left ih =>
      apply RefineF.tau_left
      exact ih ht2
    case tau_right h _ =>
      rw [tau_inj ht2]
      exact h.dest_tau_right_compat
    case zero =>
      exact RefineF.zero
    case choice_idemp h1 h2 =>
      apply RefineF.choice_idemp
      <;> rw [ht2]
      · exact h1
      · exact h2

  theorem RefineF.dest_tau_right (h : RefineF r (Refine r) t1 t2.tau) : RefineF r (Refine r) t1 t2 := by
    have := Refine.dest_tau_right (by rw [Refine]; exact h)
    rw [Refine] at this
    exact this

  theorem Refine.dest_tau (h : t1.tau ⊑r⊑ t2.tau) : t1 ⊑r⊑ t2 := by
    generalize ht1 : t1.tau = t1t at *
    generalize ht2 : t2.tau = t2t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    <;> ctree_elim ht2
    case tau h =>
      rw [tau_inj ht1, tau_inj ht2]
      rw [Refine] at h
      exact h
    case tau_left h _ =>
      rw [←ht2] at h
      rw [tau_inj ht1]
      exact h.dest_tau_right
    case tau_right h _ =>
      rw [←ht1] at h
      rw [tau_inj ht2]
      exact h.dest_tau_left

  theorem Refine.dest_tauN_left (h : tauN n t1 ⊑r⊑ t2) : t1 ⊑r⊑ t2 := by
    induction n with
    | zero =>
      simp only [tauN] at h
      exact h
    | succ n ih =>
      simp only [tauN] at h
      exact ih h.dest_tau_left

  theorem Refine.dest_tauN_right (h : t1 ⊑r⊑ tauN n t2) : t1 ⊑r⊑ t2 := by
    induction n with
    | zero =>
      simp only [tauN] at h
      exact h
    | succ n ih =>
      simp only [tauN] at h
      exact ih h.dest_tau_right

  theorem Refine.dest_ret_left {t2 : CTree ε σ} (h : Refine r (ret x) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (y : σ), t2' = ret y ∧ r x y)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (ret x ⊑r⊑ t3 ∨ ret x ⊑r⊑ t4))) := by
    generalize ht1 : ret x = t1 at h
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case ret hxy =>
      rename_i _ y
      rw [←ret_inj ht1] at hxy
      exists 0, ret y
      apply And.intro
      · simp only [tauN]
      · apply Or.inl
        exists y
    case tau_right ih =>
      have ⟨n, t2', ⟨ht2, h⟩⟩ := ih ht1
      exists n + 1, t2'
      apply And.intro _ h
      rw [ht2]
      simp only [tauN]
    case choice_left h =>
      rename_i t3 t4
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        exact Or.inl h
    case choice_right h =>
      rename_i t4 t3
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        exact Or.inr h

  theorem RefineF.dest_ret_left {t2 : CTree ε σ} (h : RefineF r (Refine r) (.ret x) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (y : σ), t2' = .ret y ∧ r x y)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (.ret x ⊑r⊑ t3 ∨ .ret x ⊑r⊑ t4))) :=
    Refine.dest_ret_left (by rw [Refine]; exact h)

  theorem Refine.dest_ret_right (h : Refine r t1 (ret y))
    : ∃ n t1', t1 = tauN n t1' ∧
        (t1' = zero
          ∨ (∃ x, t1' = ret x ∧ r x y)
          ∨ (∃ t1 t2, t1' = t1 ⊕ t2 ∧ t1 ⊑r⊑ ret y ∧ t2 ⊑r⊑ ret y)) := by
    generalize ht2 : ret y = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case ret hxy =>
      rename_i x y
      rw [ret_inj ht2]
      exists 0, ret x
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        apply Or.inl
        exists x
    case tau_left ih =>
      have ⟨n, t1', ht1, h⟩ := ih ht2
      exists n + 1, t1'
      apply And.intro _ h
      rw [ht1]
      simp only [tauN]
    case zero =>
      exists 0, zero
      apply And.intro
      · simp only [tauN]
      · exact Or.inl rfl
    case choice_idemp h1 h2 =>
      rename_i t1 t3 t2
      exists 0, t1 ⊕ t2
      apply And.intro
      · simp only [tauN]
      · repeat apply Or.inr
        exists t1, t2

  theorem Refine.dest_vis_left {e : ε α} {t2 : CTree ε σ} (h : Refine r (vis e k1) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (k2 : α → CTree ε σ), t2' = vis e k2 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (vis e k1 ⊑r⊑ t3 ∨ vis e k1 ⊑r⊑ t4))) := by
    generalize ht1 : vis e k1 = t1 at h
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case vis h =>
      rename_i k2
      have ha := vis_inj_α ht1
      subst ha
      have ⟨he, hk⟩ := vis_inj ht1
      subst he
      rw [←hk] at h
      exists 0, vis e k2
      apply And.intro
      · simp only [tauN]
      · apply Or.inl
        exists k2
    case tau_right ih =>
      have ⟨n, t2', ⟨ht2, h⟩⟩ := ih ht1
      exists n + 1, t2'
      apply And.intro _ h
      rw [ht2]
      simp only [tauN]
    case choice_left h =>
      rename_i t3 t4
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        exact Or.inl h
    case choice_right h =>
      rename_i t4 t3
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        exact Or.inr h

  theorem RefineF.dest_vis_left {e : ε α} {t2 : CTree ε σ} (h : RefineF r (Refine r) (.vis e k1) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (k2 : α → CTree ε σ), t2' = .vis e k2 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (.vis e k1 ⊑r⊑ t3 ∨ .vis e k1 ⊑r⊑ t4))) :=
    Refine.dest_vis_left (by rw [Refine]; exact h)

  theorem Refine.dest_vis_right {e : ε α} (h : Refine r t1 (vis e k2))
    : ∃ n t1', t1 = tauN n t1' ∧
        (t1' = zero
          ∨ (∃ k1, t1' = vis e k1 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
          ∨ (∃ t1 t2, t1' = t1 ⊕ t2 ∧ t1 ⊑r⊑ vis e k2 ∧ t2 ⊑r⊑ vis e k2)) := by
    generalize ht2 : vis e k2 = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case vis hk =>
      rename_i e k1 k2
      have hα := vis_inj_α ht2
      subst hα
      have ⟨he, hk⟩ := vis_inj ht2
      subst he
      subst hk
      exists 0, vis e k1
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        apply Or.inl
        exists k1
    case tau_left ih =>
      have ⟨n, t1', ht1, h⟩ := ih ht2
      exists n + 1, t1'
      apply And.intro _ h
      rw [ht1]
      simp only [tauN]
    case zero =>
      exists 0, zero
      apply And.intro
      · simp only [tauN]
      · exact Or.inl rfl
    case choice_idemp h1 h2 =>
      rename_i t1 t3 t2
      exists 0, t1 ⊕ t2
      apply And.intro
      · simp only [tauN]
      · repeat apply Or.inr
        exists t1, t2

  theorem Refine.dest_zero_right (h : Refine r t1 zero)
    : ∃ n, t1 = tauN n zero ∨ ∃ t2 t3, t1 = tauN n (t2 ⊕ t3) ∧ t2 ⊑r⊑ zero ∧ t3 ⊑r⊑ zero := by
    generalize ht2 : zero = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    rw [←ht2]
    case tau_left ih =>
      have ⟨n, h⟩ := ih ht2
      exists n + 1
      match h with
      | .inl h =>
        apply Or.inl
        rw [h]
        simp only [tauN]
      | .inr ⟨t2, t3, h⟩ =>
        apply Or.inr
        exists t2, t3
        simp only [tauN]
        apply And.intro
        · congr
          exact h.left
        · rw [ht2]
          exact h.right
    case zero =>
      exists 0
      apply Or.inl
      simp only [tauN]
    case choice_idemp h1 h2 =>
      exists 0
      apply Or.inr
      rename_i t1 _ t2
      exists t1, t2

  @[refl]
  theorem Refine.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : t ⊑r⊑ t := by
    sorry

  @[trans]
  theorem Refine.trans {r1 : Rel α β} {r2 : Rel β γ} {t1 : CTree ε α} {t2 : CTree ε β} {t3 : CTree ε γ}
    (h1 : t1 ⊑r1⊑ t2) (h2 : t2 ⊑r2⊑ t3) : t1 ⊑(r1.comp r2)⊑ t3 := by
    apply Refine.coind (λ t1 t3 => ∃ t2, t1 ⊑r1⊑ t2 ∧ t2 ⊑r2⊑ t3) _
    · exists t2
    · intro t1 t3 ⟨t2, ⟨h1, h2⟩⟩
      rw [Refine] at *
      induction h1 with
      | ret hxy =>
        have ⟨n, t3', ht3, h⟩ := h2.dest_ret_left
        rename_i y
        match h with
        | .inl ⟨z, ⟨ht3', hyz⟩⟩ =>
          rw [ht3, ht3']
          apply RefineF.tauN_right
          apply RefineF.ret
          exists y
        | .inr ⟨t3, t4, ⟨ht3', h⟩⟩ =>
          rw [ht3, ht3']
          apply RefineF.tauN_right
          cases h
          on_goal 1 =>
            apply RefineF.choice_left
          on_goal 2 =>
            apply RefineF.choice_right
          all_goals
           (exists ret y
            apply And.intro
            · rw [Refine]
              exact RefineF.ret hxy
            · assumption)
      | vis hk1 =>
        have ⟨n, t3', ⟨ht3, h⟩⟩ := h2.dest_vis_left
        rw [ht3]
        apply RefineF.tauN_right
        match h with
        | .inl ⟨k3, ht3', hk2⟩ =>
          rw [ht3']
          apply RefineF.vis
          intro a
          rename_i k2
          exists k2 a
          exact And.intro (hk1 a) (hk2 a)
        | .inr ⟨t3, t4, ht3', h⟩ =>
          rename_i e _ k2 _
          rw [ht3']
          cases h
          on_goal 1 =>
            apply RefineF.choice_left
          on_goal 2 =>
            apply RefineF.choice_right
          all_goals
           (exists vis e k2
            apply And.intro
            · rw [Refine]
              exact RefineF.vis λ a => hk1 a
            · assumption)
      | tau h1 =>
        rename_i t1 t2
        induction h2.dest_tau_left with
        | ret hyz =>
          apply RefineF.tau_left
          rename_i y z
          have h2 := h2.dest_tau_left
          have ⟨n, t1', ht1, h⟩ := h1.dest_ret_right
          match h with
          | .inl h =>
            rw [ht1, h]
            apply RefineF.tauN_left
            exact RefineF.zero
          | .inr h =>
            match h with
            | .inl ⟨x, ht1', hxy⟩ =>
              rw [ht1, ht1']
              apply RefineF.tauN_left
              apply RefineF.ret
              exists y
            | .inr ⟨t1, t2, ⟨ht1', h1, h2⟩⟩ =>
              rw [ht1, ht1']
              apply RefineF.tauN_left
              apply RefineF.choice_idemp
              all_goals (exists ret y; apply And.intro)
              on_goal 1 => exact h1
              on_goal 2 => exact h2
              all_goals (rw [Refine]; exact RefineF.ret hyz)
        | vis hk2 =>
          apply RefineF.tau_left
          rename_i e k2 k3
          have h2 := h2.dest_tau_left
          have ⟨n, t1', ht1', h⟩ := h1.dest_vis_right
          rw [ht1']
          match h with
          | .inl h =>
            rw [h]
            apply RefineF.tauN_left
            exact RefineF.zero
          | .inr h =>
            match h with
            | .inl ⟨k1, ht1', hk1⟩ =>
              rw [ht1']
              apply RefineF.tauN_left
              apply RefineF.vis
              intro a
              exists k2 a
              exact And.intro (hk1 a) (hk2 a)
            | .inr ⟨t1, t2, ht1', h1, h2⟩ =>
              rw [ht1']
              apply RefineF.tauN_left
              apply RefineF.choice_idemp
              all_goals (exists vis e k2; apply And.intro)
              on_goal 1 => exact h1
              on_goal 2 => exact h2
              all_goals (rw [Refine]; apply RefineF.vis λ a => hk2 a)
        | tau h =>
          apply RefineF.tau
          rename_i t2 _
          exists t2
          apply And.intro h1.dest_tau_right
          rw [Refine]
          exact h2.dest_tau_left.dest_tau_left.dest_tau_right
        | tau_left _ ih =>
          exact ih h1.dest_tau_right h2.dest_tau_left
        | tau_right _ ih =>
          apply RefineF.tau_right
          exact ih h1 h2.dest_tau_right
        | zero =>
          apply RefineF.tau_left
          have ⟨n, h⟩ := h1.dest_zero_right
          match h with
          | .inl h =>
            rw [h]
            apply RefineF.tauN_left
            exact RefineF.zero
          | .inr ⟨t11, t12, ht1, h1, h2⟩ =>
            rw [ht1]
            apply RefineF.tauN_left
            apply RefineF.choice_idemp
            all_goals (exists zero; apply And.intro)
            on_goal 1 => exact h1
            on_goal 2 => exact h2
            all_goals (rw [Refine]; exact RefineF.zero)
        | choice_left h =>
          rename_i t2 _ _
          apply RefineF.choice_left
          exists t2
          apply And.intro _ h
          rw [Refine] at *
          exact RefineF.tau_left h1
        | choice_right h =>
          rename_i t2 _ _
          apply RefineF.choice_right
          exists t2
          apply And.intro _ h
          rw [Refine] at *
          exact RefineF.tau_left h1
        | choice_idemp h1 h2 =>
          have h2 := h2.dest_tau_left
          apply RefineF.tau_left
          rename_i t21 t3 t22 _ _ _
          clear *- h1 h2
          sorry
      | tau_left _ ih =>
        exact RefineF.tau_left (ih h2)
      | tau_right _ ih =>
        exact ih h2.dest_tau_left
      | zero =>
        exact RefineF.zero
      | choice_left h =>
        apply dMatchOn t3
        · intro z ht3
          rename_i t21 t22
          generalize ht2 : t21 ⊕ t22 = t2 at *
          induction h2
          <;> ctree_elim ht2
          <;> ctree_elim ht3
          subst ht3
          have := (choice_inj ht2).left
          subst this
          rename_i t1 _ _ h2
          have ⟨n, t2', ⟨ht2, ht2'⟩⟩ := h2.dest_ret_right
          subst ht2
          have h1 := h.dest_tauN_right
          have h2 := h2.dest_tauN_left
          match ht2' with
          | .inl h =>
            subst h
            have ⟨n, h1⟩ := h1.dest_zero_right
            match h1 with
            | .inl h =>
              subst h
              apply RefineF.tauN_left
              exact RefineF.zero
            | .inr ⟨t1, t2, ht1, h1, h2⟩ =>
              subst ht1
              apply RefineF.tauN_left
              apply RefineF.choice_idemp <;> exists zero
          | .inr h =>
            match h with
            | .inl h =>

              sorry
            | .inr h =>
              sorry
        · sorry
        · sorry
        · sorry
        · sorry
      | choice_right => sorry
      | choice_idemp => sorry

  instance {r : Rel ρ ρ} [IsRefl ρ r] : IsRefl (CTree ε ρ) (Refine r) where
    refl := .refl

  -- TODO: Does `r` have to be refl and trans?
  instance {r : Rel ρ ρ} [IsRefl ρ r] [IsTrans ρ r] : IsTrans (CTree ε ρ) (Refine r) where
    trans := by
      intro a b c h1 h2
      have := Refine.trans h1 h2
      rw [Rel.comp_self (r := r)] at this
      exact this

  def Refine.instPreorder (r : Rel ρ ρ) [IsRefl ρ r] [IsTrans ρ r] : Preorder (CTree ε ρ) :=
  {
    le := Refine r,
    le_refl := refl,
    le_trans := by
      intro a b c h1 h2
      have := trans h1 h2
      rw [Rel.comp_self (r := r)] at this
      exact this
  }

  def Eutt (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    t1 ⊑r⊑ t2 ∧ t2 ⊑(flip r)⊑ t1

  instance {r : Rel α α} [IsRefl α r] : IsRefl α (flip r) where
    refl a := by
      simp only [flip]
      exact IsRefl.refl a

  instance {r : Rel α α} [IsTrans α r] : IsTrans α (flip r) where
    trans a b c := by
      intro h1 h2
      simp only [flip] at *
      exact IsTrans.trans _ _ _ h2 h1

  namespace Eutt
    @[refl]
    theorem refl {r : Rel ρ ρ} [IsRefl _ r] {t : CTree ε ρ} : Eutt r t t :=
      ⟨.refl _, .refl _⟩

    @[symm]
    theorem symm {r : Rel ρ ρ} [IsSymm _ r] (t1 t2 : CTree ε ρ) : Eutt r t1 t2 → Eutt r t2 t1 := by
      sorry

    @[trans]
    theorem trans {r : Rel ρ ρ} [IsRefl _ r] [IsTrans _ r] (t1 t2 t3 : CTree ε ρ) (h1 : Eutt r t1 t2) (h2 : Eutt r t2 t3) : Eutt r t1 t3 :=
      ⟨(Rel.comp_self (r := r)) ▸ .trans h1.left h2.left, (Rel.comp_self (r := flip r)) ▸ .trans h2.right h1.right⟩

    theorem choice_idemp {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} (h1 : Eutt r t1 t3) (h2 : Eutt r t2 t3)
      : Eutt r (t1 ⊕ t2) t3 := by
      apply And.intro
      · rw [Refine]
        exact RefineF.choice_idemp h1.left h2.left
      · rw [Refine]
        exact RefineF.choice_left h1.right

    theorem choice_idemp_self [IsRefl _ r] : Eutt r (t ⊕ t) t :=
      choice_idemp refl refl

    theorem choice_comm [IsRefl _ r] {t1 t2 : CTree ε ρ} : Eutt r (t1 ⊕ t2) (t2 ⊕ t1) := by
      apply And.intro
      all_goals (rw [Refine]; apply RefineF.choice_idemp; all_goals rw [Refine])
      on_goal 1 => apply RefineF.choice_right
      on_goal 2 => apply RefineF.choice_left
      on_goal 3 => apply RefineF.choice_right
      on_goal 4 => apply RefineF.choice_left
      all_goals rfl

    theorem zero_left_id [IsRefl _ r] : Eutt r (zero ⊕ t) t := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · rw [Refine]
          exact RefineF.zero
        · rfl
      · apply RefineF.choice_right
        rfl

    theorem zero_right_id [IsRefl _ r] : Eutt r (t ⊕ zero) t := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · rfl
        · rw [Refine]
          exact RefineF.zero
      · apply RefineF.choice_left
        rfl

    theorem choice_assoc [IsRefl _ r] : Eutt r ((t1 ⊕ t2) ⊕ t3) (t1 ⊕ (t2 ⊕ t3)) := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · rw [Refine]
          apply RefineF.choice_idemp
          · rw [Refine]
            apply RefineF.choice_left
            rfl
          · rw [Refine]
            apply RefineF.choice_right
            rw [Refine]
            apply RefineF.choice_left
            rfl
        · rw [Refine]
          apply RefineF.choice_right
          rw [Refine]
          apply RefineF.choice_right
          rfl
      · apply RefineF.choice_idemp
        · rw [Refine]
          apply RefineF.choice_left
          rw [Refine]
          apply RefineF.choice_left
          rfl
        · rw [Refine]
          apply RefineF.choice_idemp
          · rw [Refine]
            apply RefineF.choice_left
            rw [Refine]
            apply RefineF.choice_right
            rfl
          · rw [Refine]
            apply RefineF.choice_right
            rfl

  end Eutt

  instance [IsEquiv _ r] : IsEquiv (CTree ε ρ) (Eutt r) where
     refl := @Eutt.refl _ _ _ _
     trans := Eutt.trans
     symm := Eutt.symm

  instance : HasEquiv (CTree ε ρ) where
    Equiv := Eutt Eq

  /- Paralle Opeartor -/

  def vis_left {α β} (par : CTree ε α → CTree ε β → CTree ε (α × β))
    (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  def bothRet (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  -- TODO: How to do the case with two events?
  def biasedEffect (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry
    -- corec' (λ rec (t1, t2) =>
    --   match t1.dest with
    --   | ⟨.ret a, _⟩ => .inl <| zero
    --   | ⟨.tau, c⟩ => .inr <| tau' <| rec (c _fin0, t2)
    --   | ⟨.zero, _⟩ => .inl <| zero
    --   | ⟨.choice, cts⟩ => .inr <| choice' (rec ⟨cts _fin0, t2⟩) (rec (cts _fin1, t2))
    --   | ⟨.vis α e, k⟩ =>
    --     .inr <| vis' e λ a =>
    --       let k := k (.up a)
    --       choice' (rec ⟨k, t2⟩) (bothRet k t2)
    -- ) (t1, t2)
    -- corec (α := sorry) (λ state => sorry) sorry
    -- corec' (λ {X} rec (t1, t2) =>
    --   match t1.dest, t2.dest with
    --   | ⟨.ret a, _⟩, ⟨.ret b, _⟩ => .inl <| ret (a, b)
    --   | ⟨.tau, c⟩, _ => .inr <| tau' <| rec (c _fin0, t2)
    --   | _, ⟨.tau, c⟩ => .inr <| tau' <| rec (t1, c _fin0)
    --   | ⟨.choice, cts⟩, _ => .inr <| choice' (rec ⟨cts _fin0, t2⟩) (rec (cts _fin1, t2))
    --   | _, ⟨.choice, cts⟩ => .inr <| choice' (rec ⟨t1, cts _fin0⟩) (rec (t1, cts _fin1))
    --   | ⟨.vis α1 e1, k1⟩, ⟨.vis α2 e2, k2⟩ =>
    --     let left : P ε (α × β) X := vis' e1 λ a => rec ⟨k1 (.up a), t2⟩
    --     let right : P ε (α × β) X := vis' e2 λ a => rec ⟨t1, k2 (.up a)⟩
    --     .inr <| choice' sorry sorry
    --   | ⟨.vis α' e, k⟩, _ => .inr <| vis' e λ a => rec ⟨k (.up a), t2⟩
    --   | _, ⟨.vis α' e, k⟩ => .inr <| vis' e λ a => rec ⟨t1, k (.up a)⟩
    --   | _, _ => .inl zero
    -- ) (t1, t2)

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry
  infixr:60 " || " => par

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 || t2)
  infixr:60 " ||→ " => parR

  namespace Eutt
    theorem parR_ret : Eutt r ((ret x) ||→ t) t := by
      sorry

    theorem parR_map : Eutt r ((map f t1) ||→ t2) (t1 ||→ t2) := by
      sorry

    theorem parR_assoc : Eutt r ((t1 ||→ t2) ||→ t3) (t1 ||→ (t2 ||→ t3)) := by
      sorry

    theorem parR_symm : Eutt r ((t1 ||→ t2) ||→ t3) ((t2 ||→ t1) ||→ t3) := by
      sorry
  end Eutt

  end
end CTree

def parametricFun (E : Type → Type) (F : Type → Type) :=
  ∀ α : Type, E α → F α
infixr:50 " ⟹ "=> parametricFun
