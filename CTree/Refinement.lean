import CTree.Basic
import Mathlib.Data.Nat.PartENat


namespace CTree
  /--
    Somewhat failed attemp at defining a direct refinement between `CTree`s without defining traces first.
    The definition uses ideas from the [FreeSim paper](https://dl.acm.org/doi/10.1145/3622857)

    While this definition seems plausible and we can prove reflexivity and an intersting theorem about infinite non-determinism.
    This nested inductive-coinductive structure is very difficult to work with in practice compared to `TraceRefine` (at least
    for writing general equational theories, ymmv when proving equivalence of concrete systems).

    Note that this is not equivalent to `TraceRefine`, becasuse `TraceRefine` makes no distinction between `zero` and `infND`.
  -/
  inductive RefineF {ε : Type → Type} {ρ σ : Type}
    (r : Rel ρ σ) (sim : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop)
    : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop
  | coind {p1 p2 t1 t2} (p1' p2' : PartENat)
      (h1 : p1' < p1) (h2 : p2' < p2) (h : sim p1' p2' t1 t2)
      : RefineF r sim p1 p2 t1 t2
  | ret {x y p1 p2} (h : r x y) : RefineF r sim p1 p2 (ret x) (ret y)
  | vis {p1 p2} {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, RefineF r sim ⊤ ⊤ (k1 a) (k2 a)) : RefineF r sim p1 p2 (vis e k1) (vis e k2)
  | tau_left {p1 p2 t1 t2}
      (h : RefineF r sim ⊤ p2 t1 t2) : RefineF r sim p1 p2 t1.tau t2
  | tau_right {p1 p2 t1 t2}
      (h : RefineF r sim p1 ⊤ t1 t2) : RefineF r sim p1 p2 t1 t2.tau
  | zero {p1 p2} {t : CTree ε σ} : RefineF r sim p1 p2 zero t
  | choice_left {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 ⊤ t1 t2) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_right {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 ⊤ t1 t3) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_idemp {p1 p2 t1 t2 t3}
      (h1 : RefineF r sim ⊤ p2 t1 t3) (h2 : RefineF r sim ⊤ p2 t2 t3)
      : RefineF r sim p1 p2 (t1 ⊕ t2) t3

  def Refine' (r : Rel ρ σ) (p1 p2 : PartENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    RefineF r (Refine' r) p1 p2 t1 t2
    greatest_fixpoint monotonicity by
      intro _ _ hsim _ _ _ _ h
      induction h with
      | coind _ _ h1 h2 h => exact .coind _ _ h1 h2 (hsim _ _ _ _ h)
      | ret h => exact .ret h
      | vis _ ih => exact .vis λ a => ih a
      | tau_left _ ih => exact RefineF.tau_left ih
      | tau_right _ ih => exact RefineF.tau_right ih
      | zero => exact .zero
      | choice_left _ ih => exact .choice_left ih
      | choice_right _ ih => exact .choice_right ih
      | choice_idemp _ _ ih1 ih2 => exact .choice_idemp ih1 ih2

  abbrev Refine (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
    ∃ p1 p2, Refine' r p1 p2 t1 t2

  -- `t1 r⊑ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ⊑"r:61"⊑ " t2:61 => Refine r t1 t2

  theorem Refine.coind (sim : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop) (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
    (p1 p2 : PartENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : t1 ⊑r⊑ t2 :=
    ⟨p1, ⟨p2, Refine'.fixpoint_induct r sim adm p1 p2 t1 t2 h⟩⟩

  @[refl]
  theorem Refine.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : t ⊑r⊑ t := by
    apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ t1 = t2) _ 0 0 (And.intro rfl <| And.intro rfl rfl)
    intro p1 p2 t t' h
    obtain ⟨hp1, hp2, heq⟩ := h
    subst hp1
    subst hp2
    subst heq
    apply dMatchOn t
    · intro v heq
      subst heq
      apply RefineF.ret
      exact IsRefl.refl v
    · intro c heq
      subst heq
      apply RefineF.tau_left
      apply RefineF.tau_right
      apply RefineF.coind 0 0
      <;> simp_all only [PartENat.zero_lt_top]
      simp_all only [and_self]
    · intro α e k heq
      subst heq
      apply RefineF.vis
      intro a
      apply RefineF.coind 0 0
      <;> simp_all only [PartENat.zero_lt_top]
      simp_all only [and_self]
    · intro heq
      subst heq
      exact RefineF.zero
    · intro c1 c2 heq
      subst heq
      apply RefineF.choice_idemp
      · apply RefineF.choice_left
        apply RefineF.coind 0 0
        <;> simp_all only [PartENat.zero_lt_top]
        simp_all only [and_self]
      · apply RefineF.choice_right
        apply RefineF.coind 0 0
        <;> simp_all only [PartENat.zero_lt_top]
        simp_all only [and_self]

  inductive IsInfF (sim : CTree ε ρ → Prop) : CTree ε ρ → Prop
  | choice_left (h : sim t1) : IsInfF sim (t1 ⊕ t2)
  | choice_right (h : sim t2) : IsInfF sim (t1 ⊕ t2)
  | tau (h : sim t) : IsInfF sim t.tau

  def IsInf (t : CTree ε ρ) : Prop :=
    IsInfF IsInf t
    greatest_fixpoint monotonicity by
      intro sim1 sim2 hsim x h
      cases h with
      | choice_left h => exact .choice_left (hsim _ h)
      | choice_right h => exact .choice_right (hsim _ h)
      | tau h => exact .tau (hsim _ h)

  theorem infND_refine_left : infND ⊑r⊑ t → IsInf t := by
    intro h
    apply IsInf.fixpoint_induct (λ t => infND ⊑r⊑ t) _ t h
    intro t h
    rw [Refine] at h
    obtain ⟨p1, p2, h⟩ := h
    revert p1
    induction p2 using WellFounded.induction PartENat.lt_wf
    rename_i p2 ihp2
    intro p2 h
    rw [Refine'] at h
    rw [infND_eq] at h
    generalize hinf : infND ⊕ infND = t at *
    induction h
    <;> ctree_elim hinf
    case coind _ p2 _ h2 h =>
      rw [←hinf, ←infND_eq] at h
      exact ihp2 p2 h2 _ h
    case tau_right h _ =>
      apply IsInfF.tau
      subst hinf
      rw [←infND_eq] at h
      rename_i p1 _ _ _
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_left h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_left
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_right h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_right
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_idemp h1 h2 ih1 ih2 =>
      apply ih2 ihp2
      rw [←(choice_inj hinf).right]
      simp only [←infND_eq]

end CTree
