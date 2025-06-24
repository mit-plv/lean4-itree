import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3
import Mathlib.Data.Rel
import CTree.Utils

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

/--
Coinductive Choice Tree defined with `PFunctor.M`.
Equivalent to the following definition:
```
coinductive CTree (ε : Type → Type) (ρ : Type)
| ret (v : ρ)
| tau (t : CTree ε ρ)
| vis {α : Type} (e : ε α) (k : α → CTree ε ρ)
| zero
| choice (l r : CTree ε ρ)
```
-/
def CTree (ε : Type → Type) (ρ : Type) := (CTree.P ε ρ).M

namespace CTree
  section
  variable {ε : Type → Type} {ρ : Type}

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

  /- Injectivity of the constructors -/
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

  macro "subst_vis_inj " h:term : tactic => `(tactic|(
    have hα := vis_inj_α $h
    subst hα
    have ⟨he, hk⟩ := vis_inj $h
    subst he hk
  ))

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

  /-- Infinite Taus -/
  def infTau : CTree ε ρ :=
    corec' (α := PUnit) (λ rec x =>
      .inr <| CTree.tau' (rec x)
    ) PUnit.unit

  theorem infTau_eq : @infTau ε ρ = tau infTau := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = infTau ∧ t2 = tau infTau) _
    · apply And.intro <;> rfl
    · intro x y ⟨hx, hy⟩
      simp only [infTau, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, tau',
        Function.comp_apply, id_eq, PFunctor.map, Function.id_comp, PFunctor.M.corec_def] at hx
      simp only [tau, mk, tau', infTau, corec', PFunctor.M.corec', PFunctor.M.corec₁, bind,
        Sum.bind, Function.comp_apply, id_eq, PFunctor.map, Function.id_comp,
        PFunctor.M.corec_def] at hy
      subst hx hy
      simp only [PFunctor.M.dest_mk]
      apply exists_and_eq
      intro i
      apply And.intro
      · match i with
        | .up (.ofNat' 0) =>
          simp only [Fin2.ofNat', Function.comp_apply, infTau, corec', PFunctor.M.corec',
            PFunctor.M.corec₁, bind, Sum.bind, tau', id_eq, PFunctor.map, Function.id_comp]
          rfl
      · match i with
        | .up (.ofNat' 0) =>
          simp only [_fin1Const, Fin2.ofNat', tau, mk, tau']
          congr
          funext i
          match i with
          | .up (.ofNat' 0) =>
            simp only [Fin2.ofNat', Function.comp_apply, _fin1Const, infTau, corec',
              PFunctor.M.corec', PFunctor.M.corec₁, bind, Sum.bind, tau', id_eq, PFunctor.map,
              Function.id_comp]

  /-- Infinite Nondeterminism -/
  def infND : CTree ε ρ :=
    corec' (α := PUnit) (λ rec x =>
      .inr <| CTree.choice' (rec x) (rec x)
    ) PUnit.unit

  theorem infND_eq : @infND ε ρ = (infND ⊕ infND) := by
    apply PFunctor.M.bisim (λ t1 t2 => t1 = infND ∧ t2 = (infND ⊕ infND)) _
    · apply And.intro <;> rfl
    · intro x y h
      have ⟨hx, hy⟩ := h
      simp only [infND, corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
        PFunctor.map, Bind.bind, Sum.bind, choice'] at hx
      simp only [infND, corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
        PFunctor.map, Bind.bind, Sum.bind, choice'] at hy
      rw [hx, hy]
      simp only [PFunctor.M.dest_mk]
      apply exists_and_eq
      intro i
      apply And.intro
      · match i with
        | .up (.ofNat' 0) =>
          simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
            Nat.reduceAdd, Vector3.cons_fz, infND, corec', PFunctor.M.corec', PFunctor.M.corec₁,
            Bind.bind, Sum.bind, choice', PFunctor.map]
        | .up (.ofNat' 1) =>
          simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
            Nat.reduceAdd, Vector3.cons_fs, Vector3.cons_fz, infND, corec', PFunctor.M.corec',
            PFunctor.M.corec₁, Bind.bind, Sum.bind, choice', PFunctor.map]
      · match i with
        | .up (.ofNat' 0) =>
          simp only [choice, mk, choice', PFunctor.M.children_mk, cast_eq, _fin2Const, Fin2.ofNat', Vector3.cons, Fin2.cases']
          congr
          funext i
          match i with
          | .up (.ofNat' 0) =>
            simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
              Nat.reduceAdd, Vector3.cons_fz, infND, corec', PFunctor.M.corec', PFunctor.M.corec₁,
              Bind.bind, Sum.bind, choice', PFunctor.map]
          | .up (.ofNat' 1) =>
            simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
              Nat.reduceAdd, Vector3.cons_fs, Vector3.cons_fz, infND, corec', PFunctor.M.corec',
              PFunctor.M.corec₁, Bind.bind, Sum.bind, choice', PFunctor.map]
        | .up (.ofNat' 1) =>
          simp only [choice, mk, choice', PFunctor.M.children_mk, cast_eq, _fin2Const, Fin2.ofNat', Vector3.cons, Fin2.cases']
          congr
          funext i
          match i with
          | .up (.ofNat' 0) =>
            simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
              Nat.reduceAdd, Vector3.cons_fz, infND, corec', PFunctor.M.corec', PFunctor.M.corec₁,
              Bind.bind, Sum.bind, choice', PFunctor.map]
          | .up (.ofNat' 1) =>
            simp only [Function.comp_apply, id_eq, Function.id_comp, Fin2.ofNat', _fin2Const,
              Nat.reduceAdd, Vector3.cons_fs, Vector3.cons_fz, infND, corec', PFunctor.M.corec',
              PFunctor.M.corec₁, Bind.bind, Sum.bind, choice', PFunctor.map]

  def KTree (ε : Type → Type) (α β : Type) : Type 1 := α → CTree ε β

  inductive State (ε : Type → Type) (ρ : Type)
  | ct : CTree ε ρ → State ε ρ
  | kt {α} : KTree ε α ρ → State ε ρ

  notation:150 "C[ " t " ]" => State.ct t
  notation:150 "K[ " t " ]" => State.kt t
  notation:151 "K[ " α' " | " t " ]" => State.kt (α := α') t

  inductive ContainsRet (v : ρ) : CTree ε ρ → Prop
  | ret : ContainsRet v (ret v)
  | tau {t} : ContainsRet v t → ContainsRet v t.tau
  | choice_left {t1 t2} : ContainsRet v t1 → ContainsRet v (t1 ⊕ t2)
  | choice_right {t1 t2} : ContainsRet v t2 → ContainsRet v (t1 ⊕ t2)

  inductive ContainsVis {α : Type} (e : ε α) (k : α → CTree ε ρ) : CTree ε ρ → Prop
  | vis : ContainsVis e k (vis e k)
  | tau {t} : ContainsVis e k t → ContainsVis e k t.tau
  | choice_left {t1 t2} : ContainsVis e k t1 → ContainsVis e k (t1 ⊕ t2)
  | choice_right {t1 t2} : ContainsVis e k t2 → ContainsVis e k (t1 ⊕ t2)

  inductive TerminateNoVis : CTree ε ρ → Prop
  | zero : TerminateNoVis zero
  | ret {v} : TerminateNoVis (ret v)
  | tau {t} : TerminateNoVis t → TerminateNoVis t.tau
  | choice {c1 c2} : TerminateNoVis c1 → TerminateNoVis c2 → TerminateNoVis (c1 ⊕ c2)

  /--
  `ctree_elim heq` where `heq` is an equality between `CTree`s tries to to prove `False` using `heq`.
  -/
  macro "ctree_elim " h:term : tactic => `(tactic|(
    try (have := (Sigma.mk.inj (PFunctor.M.mk_inj $h)).left; contradiction)
  ))

  end
end CTree
