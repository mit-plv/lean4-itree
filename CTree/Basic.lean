import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3
import Mathlib.Data.Rel
import CTree.Utils
import CTree.Paco

inductive CTree.shape (ε : Type u1 → Type v) (ρ : Type u2)
  : Type (max (max (u1 + 1) u2) v)
  | ret (v : ρ)
  | tau
  | vis (α : Type u1) (e : ε α)
  | zero
  | choice

def CTree.children.{u1, v1, u2} {ε : Type u1 → Type v1} {ρ : Type u2}
  : CTree.shape ε ρ → Type u1
  | .ret _ => ULift (Fin2 0)
  | .tau => ULift (Fin2 1)
  | .vis α _ => α
  | .zero => ULift (Fin2 0)
  | .choice => ULift (Fin2 2)

def CTree.P.{u1, v1, u2} (ε : Type u1 → Type v1) (ρ : Type u2) : PFunctor :=
  ⟨CTree.shape.{u1, v1, u2} ε ρ, CTree.children.{u1, v1, u2}⟩

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
def CTree (ε : Type u1 → Type v) (ρ : Type u2) :=
  (CTree.P ε ρ).M

namespace CTree
  section
  variable {ε : Type u1 → Type v1} {ρ : Type u2}

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
  def vis' {α : Type u1} (e : ε α) (k : α → X) : P ε ρ X :=
    .mk (.vis α e) (k ·)

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
  def vis {α : Type u1} (e : ε α) (k : α → CTree ε ρ) : CTree ε ρ :=
    .mk <| vis' e k

  @[match_pattern, simp]
  def zero : CTree ε ρ :=
    .mk zero'

  @[match_pattern, simp]
  def choice (t1 t2 : CTree ε ρ) : CTree ε ρ :=
    .mk <| choice' t1 t2
  infixr:70 " ⊕ " => CTree.choice

  def trigger {α : Type u1} (e : ε α) : CTree ε α :=
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
      have := congr (a₁ := x) this rfl
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

  def matchOn {motive : Sort u} (x : CTree ε ρ)
    (ret : (v : ρ) → motive)
    (tau : (c : CTree ε ρ) → motive)
    (vis : {α : Type u1} → (e : ε α) → (k : α → CTree ε ρ) → motive)
    (zero : motive)
    (choice : (c1 c2 : CTree ε ρ) → motive)
    : motive :=
    match x.dest with
    | ⟨.ret v, _⟩ =>
      ret v
    | ⟨.tau, c⟩ =>
      tau (c _fin0)
    | ⟨.vis _ e, k⟩ =>
      vis e k
    | ⟨.zero, _⟩ =>
      zero
    | ⟨.choice, cs⟩ =>
      choice (cs _fin0) (cs _fin1)

  /-- Custom dependent match function for CTrees -/
  def dMatchOn {motive : CTree ε ρ → Sort u} (x : CTree ε ρ)
    (ret : (v : ρ) → x = ret v → motive x)
    (tau : (c : CTree ε ρ) → x = tau c → motive x)
    (vis : (α : Type u1) → (e : ε α) → (k : α → CTree ε ρ) → x = vis e k → motive x)
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
      vis α e k (by
        simp only [CTree.vis, vis', mk]
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

  theorem dest_vis : PFunctor.M.dest (F := P ε ρ) (vis e k) = ⟨.vis _ e, k⟩ :=
    rfl

  theorem dest_zero : PFunctor.M.dest (F := P ε ρ) zero = ⟨.zero, _elim0⟩ :=
    rfl

  theorem dest_choice : PFunctor.M.dest (F := P ε ρ) (choice c1 c2) = ⟨.choice, _fin2Const c1 c2⟩ :=
    rfl

  /-- Infinite Taus -/
  def infTau : CTree ε ρ :=
    PFunctor.M.corec' (λ rec x =>
      .inr <| CTree.tau' (rec x)
    ) ()

  theorem infTau_eq : @infTau ε ρ = tau infTau := by
    conv =>
      lhs
      simp [infTau]
    rw [unfold_corec']
    simp only [tau, tau']
    congr
    funext
    rename_i i
    match i with
    | .up (.ofNat' 0) => rfl

  /-- Infinite Nondeterminism -/
  def infND : CTree ε ρ :=
    PFunctor.M.corec' (λ rec x =>
      .inr <| CTree.choice' (rec x) (rec x)
    ) ()

  theorem infND_eq : @infND ε ρ = (infND ⊕ infND) := by
    conv =>
      lhs
      simp [infND]
    rw [unfold_corec']
    simp only [choice, choice']
    congr
    funext
    rename_i i
    match i with
    | .up (.ofNat' 0) => rfl
    | .up (.ofNat' 1) => rfl

  def KTree (ε : Type u1 → Type v1) (α β : Type u2) := α → CTree ε β

  inductive State (ε : Type u1 → Type v1) (ρ : Type u2)
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

  inductive ContainsVis {ε : Type u1 → Type v1} {α : Type u1} (e : ε α) (k : α → CTree ε ρ) : CTree ε ρ → Prop
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

  inductive eqF (sim : CTree ε ρ → CTree ε ρ → Prop) : CTree ε ρ → CTree ε ρ → Prop
  | eq_ret v : eqF sim (ret v) (ret v)
  | eq_vis {α} e k1 k2 (h : ∀ a : α, sim (k1 a) (k2 a)) : eqF sim (vis e k1) (vis e k2)
  | eq_tau t1 t2 (h : sim t1 t2) : eqF sim (tau t1) (tau t2)
  | eq_zero : eqF sim zero zero
  | eq_choice t11 t12 t21 t22 (h1 : sim t11 t21) (h2 : sim t12 t22) : eqF sim (t11 ⊕ t12) (t21 ⊕ t22)

  lemma eqF_inv (sim : CTree ε ρ → CTree ε ρ → Prop) t1 t2 (h : eqF sim t1 t2) :
    (∃ v, t1 = ret v ∧ t2 = ret v) ∨
    (∃ α, ∃ e : ε α, ∃ k1, ∃ k2, (∀ a : α, sim (k1 a) (k2 a)) ∧ t1 = vis e k1 ∧ t2 = vis e k2) ∨
    (∃ t1', ∃ t2', sim t1' t2' ∧ t1 = tau t1' ∧ t2 = tau t2') ∨
    (t1 = zero ∧ t2 = zero) ∨
    (∃ t11, ∃ t12, ∃ t21, ∃ t22, sim t11 t21 ∧ sim t12 t22 ∧ t1 = t11 ⊕ t12 ∧ t2 = t21 ⊕ t22) := by
    cases h
    · left
      repeat (on_goal 1 => apply Exists.intro)
      exact ⟨rfl, rfl⟩
    · right; left
      repeat (on_goal 1 => apply Exists.intro)
      rename_i h; exact ⟨h, ⟨rfl, rfl⟩⟩
    · right; right; left
      repeat (on_goal 1 => apply Exists.intro)
      rename_i h; exact ⟨h, ⟨rfl, rfl⟩⟩
    · right; right; right; left
      exact ⟨rfl, rfl⟩
    · right; right; right; right
      repeat (on_goal 1 => apply Exists.intro)
      rename_i h1 h2; exact ⟨h1, ⟨h2, ⟨rfl, rfl⟩⟩⟩

  theorem eqF_monotone sim sim' (hsim : ∀ (t1 t2 : CTree ε ρ), sim t1 t2 → sim' t1 t2) :
    ∀ t1 t2, eqF sim t1 t2 → eqF sim' t1 t2 := by
    intros t1 t2 h
    cases h <;> constructor <;> intros <;> apply hsim <;> try assumption
    rename_i h _; apply h

  def eq (t1 t2 : CTree ε ρ) : Prop :=
    eqF eq t1 t2
    coinductive_fixpoint monotonicity fun sim' sim hsim =>
      eqF_monotone sim sim' hsim

  theorem eq_eq (t1 t2 : CTree ε ρ) : eq t1 t2 ↔ t1 = t2 := by
    constructor
    · intro h
      apply PFunctor.M.bisim (λ t1 t2 => eq t1 t2) <;> try assumption
      intro t1
      apply CTree.dMatchOn (x := t1) <;>
        (intros; rename_i h _ _; subst h; rename_i t2 h; revert h; apply CTree.dMatchOn (x := t2)) <;>
        (intros; rename_i h _; subst h; rename_i h; simp only [CTree.eq] at h) <;>
        try (apply eqF_inv at h; cases h; on_goal 1 =>
          rename_i h; have ⟨_, ⟨h1, h2⟩⟩ := h; try solve | ctree_elim h1 | ctree_elim h2) <;>
        try (rename_i h; cases h; on_goal 1 =>
          rename_i h; have ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨h1, h2⟩⟩⟩⟩⟩⟩ := h; try solve | ctree_elim h1 | ctree_elim h2) <;>
        try (rename_i h; cases h; on_goal 1 =>
          rename_i h; have ⟨_, ⟨_, ⟨_, ⟨h1, h2⟩⟩⟩⟩ := h; try solve | ctree_elim h1 | ctree_elim h2) <;>
        try (rename_i h; cases h; on_goal 1 =>
          rename_i h; have ⟨h1, h2⟩ := h; try solve | ctree_elim h1 | ctree_elim h2) <;>
        try (rename_i h; on_goal 1 =>
          rename_i h; have ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨h1, h2⟩⟩⟩⟩⟩⟩⟩ := h; try solve | ctree_elim h1 | ctree_elim h2)
      · apply ret_inj at h1; apply ret_inj at h2; subst h1 h2
        repeat (on_goal 1 => apply Exists.intro)
        apply And.intro rfl; apply And.intro rfl; intros i; cases i; rename_i i; cases i
      · apply tau_inj at h1; apply tau_inj at h2; subst h1 h2
        repeat (on_goal 1 => apply Exists.intro)
        apply And.intro rfl; apply And.intro rfl; intros i
        simp only [tau, mk, tau', PFunctor.M.children_mk]
        match i with
        | .up (.ofNat' 0) =>
          simp only [_fin1Const, cast_eq, Fin2.ofNat']
          assumption
      · have h1' := vis_inj_α h1; subst h1'
        have h2' := vis_inj_α h2; subst h2'
        have ⟨h1, h1'⟩ := vis_inj h1; subst h1 h1'
        have ⟨h2, h2'⟩ := vis_inj h2; subst h2 h2'
        repeat (on_goal 1 => apply Exists.intro)
        apply And.intro rfl; apply And.intro rfl; intros a
        rename_i h; apply h
      · repeat (on_goal 1 => apply Exists.intro)
        apply And.intro rfl; apply And.intro rfl; intros i; cases i; rename_i i; cases i
      · have ⟨h1, h1'⟩ := choice_inj h1; subst h1 h1'
        have ⟨h2, h2'⟩ := choice_inj h2; subst h2 h2'
        repeat (on_goal 1 => apply Exists.intro)
        apply And.intro rfl; apply And.intro rfl; intros i
        simp only [choice, mk, choice', PFunctor.M.children_mk]
        match i with
        | .up (.ofNat' 0) =>
          simp only [_fin2Const, cast_eq, Fin2.ofNat']
          assumption
        | .up (.ofNat' 1) =>
          simp only [_fin2Const, cast_eq, Fin2.ofNat']
          assumption
    · intro h; subst h
      revert t1
      pcofix cih
      intros t1
      pfold
      apply t1.dMatchOn <;> intros <;> rename_i h <;> subst h <;> constructor
      all_goals (intros; pleft; apply cih)

    theorem eq_refl {sim} {hsim : ∀ t1 t2, eq t1 t2 → sim t1 t2} (t : CTree ε ρ) : eqF sim t t := by
      apply eqF_monotone <;> try assumption
      rw [← eq, eq_eq]
  end
end CTree
