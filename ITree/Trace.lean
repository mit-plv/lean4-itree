import CTree.Basic
import CTree.Monad

namespace CTree
  inductive Trace (ε : Type u → Type v) (ρ : Type w)
  | nil : Trace ε ρ
  | ret (v : ρ) : Trace ε ρ
  | event_end {α} (e : ε α) : Trace ε ρ
  | event_response {α} (e : ε α) (a : α) (cont : Trace ε ρ) : Trace ε ρ

  inductive IsTraceOf {ε : Type u → Type v} {ρ : Type w} : Rel (CTree ε ρ) (Trace ε ρ)
  | empty {t} : IsTraceOf t .nil
  | ret (v) : IsTraceOf (.ret v) (.ret v)
  | tau {t} (tr) : IsTraceOf t tr → IsTraceOf t.tau tr
  | vis_end {α} {k : α → CTree ε ρ} (e : ε α)
      : IsTraceOf (.vis e k) (.event_end e)
  | vis_continue {α} (tr) {k : α → CTree ε ρ} (e : ε α) (a : α)
      : IsTraceOf (k a) tr → IsTraceOf (.vis e k) (.event_response e a tr)
  | choice_left {t1 t2} (tr) : IsTraceOf t1 tr → IsTraceOf (t1 ⊕ t2) tr
  | choice_right {t1 t2} (tr) : IsTraceOf t2 tr → IsTraceOf (t1 ⊕ t2) tr

  def TraceRefine {ε ρ} (t1 t2 : CTree ε ρ) : Prop :=
    ∀ (tr : Trace ε ρ), IsTraceOf t1 tr → IsTraceOf t2 tr

  infix:60 " ⊑ " => TraceRefine

  theorem TraceRefine.ret_le {t : CTree ε ρ} (h : .ret v ⊑ t) : t.IsTraceOf (.ret v) := by
    exact h (.ret v) (.ret v)

  theorem TraceRefine.ret_le_choice {t1 t2 : CTree ε ρ} (h : .ret v ⊑ t1 ⊕ t2) : t1.IsTraceOf (.ret v) ∨ t2.IsTraceOf (.ret v) := by
    have h := h (.ret v) (.ret v)
    generalize ht : t1 ⊕ t2 = t at *
    cases h
    <;> ctree_elim ht
    case choice_left h =>
      rw [(choice_inj ht).left]
      exact Or.inl h
    case choice_right h =>
      rw [(choice_inj ht).right]
      exact Or.inr h

  theorem TraceRefine.choice_le {t1 t2 t3 : CTree ε ρ} (h : (t1 ⊕ t2) ⊑ t3) : t1 ⊑ t3 ∧ t2 ⊑ t3 := by
    apply And.intro
    · intro tr h
      cases h with
      | empty => exact .empty
      | ret v => exact h (.ret v) (.choice_left _ (.ret v))
      | tau tr htr => exact h tr (.choice_left _ (.tau _ htr))
      | vis_end e => exact h (.event_end e) (.choice_left _ (.vis_end e))
      | vis_continue tr e a htr => exact h (.event_response e a tr) (.choice_left _ (.vis_continue tr e a htr))
      | choice_left tr htr => exact h tr (.choice_left _ (.choice_left _ htr))
      | choice_right tr htr => exact h tr (.choice_left _ (.choice_right _ htr))
    · intro tr h
      cases h with
      | empty => exact .empty
      | ret v => exact h (.ret v) (.choice_right _ (.ret v))
      | tau tr htr => exact h tr (.choice_right _ (.tau _ htr))
      | vis_end e => exact h (.event_end e) (.choice_right _ (.vis_end e))
      | vis_continue tr e a htr => exact h (.event_response e a tr) (.choice_right _ (.vis_continue tr e a htr))
      | choice_left tr htr => exact h tr (.choice_right _ (.choice_left _ htr))
      | choice_right tr htr => exact h tr (.choice_right _ (.choice_right _ htr))

  @[refl]
  theorem TraceRefine.refl {t : CTree ε ρ} : t ⊑ t := by
    intro tr h
    simp_all only

  @[trans]
  theorem TraceRefine.trans {t1 t2 t3 : CTree ε ρ} (h1 : t1 ⊑ t2) (h2 : t2 ⊑ t3) : t1 ⊑ t3 := by
    intro tr htr
    induction htr with
    | empty => exact .empty
    | ret v =>
      cases h1 (.ret v) (.ret v)
      case ret => exact ret_le h2
      case tau h1 => exact h2 (.ret v) (.tau _ h1)
      all_goals
       (apply h1.ret_le_choice.elim <;> intro h
        · exact h2.choice_le.left (.ret v) h
        · exact h2.choice_le.right (.ret v) h)
    | tau _ _ ih => exact ih λ tr htr => h1 tr (.tau _ htr)
    | vis_end e =>
      cases h1 (.event_end e) (.vis_end e)
      case tau h => exact h2 (.event_end e) (.tau _ h)
      case vis_end => exact h2 (.event_end e) (.vis_end e)
      case choice_left h => exact h2 (.event_end e) (.choice_left _ h)
      case choice_right h => exact h2 (.event_end e) (.choice_right _ h)
    | vis_continue tr e a h =>
      cases h1 (.event_response e a tr) (.vis_continue tr e a h)
      case tau h => exact h2 (.event_response e a tr) (.tau _ h)
      case vis_continue h => exact h2 (.event_response e a tr) (.vis_continue tr e a h)
      case choice_left h => exact h2 (.event_response e a tr) (.choice_left _ h)
      case choice_right h => exact h2 (.event_response e a tr) (.choice_right _ h)
    | choice_left _ _ ih => exact ih h1.choice_le.left
    | choice_right _ _ ih => exact ih h1.choice_le.right

  theorem TraceRefine.choice_idemp {t1 t2 t3 : CTree ε ρ} (h1 : t1 ⊑ t3) (h2 : t2 ⊑ t3) : (t1 ⊕ t2) ⊑ t3 := by
    intro tr h
    generalize ht : t1 ⊕ t2 = t at *
    cases h
    <;> ctree_elim ht
    case empty => exact .empty
    case choice_left h =>
      rw [←(choice_inj ht).left] at h
      exact h1 tr h
    case choice_right h =>
      rw [←(choice_inj ht).right] at h
      exact h2 tr h

  theorem TraceRefine.choice_le_iff {t1 t2 t3 : CTree ε ρ} : (t1 ⊕ t2) ⊑ t3 ↔ t1 ⊑ t3 ∧ t2 ⊑ t3 :=
    ⟨TraceRefine.choice_le, λ h => TraceRefine.choice_idemp h.left h.right⟩

  theorem TraceRefine.choice_left {t1 t2 t3 : CTree ε ρ} (h : t1 ⊑ t2) : t1 ⊑ t2 ⊕ t3 :=
    λ tr htr => IsTraceOf.choice_left _ (h tr htr)

  theorem TraceRefine.choice_right {t1 t2 t3 : CTree ε ρ} (h : t1 ⊑ t3) : t1 ⊑ t2 ⊕ t3 :=
    λ tr htr => IsTraceOf.choice_right _ (h tr htr)

  theorem TraceRefine.zero_le : zero ⊑ t := by
    intro tr htr
    generalize hz : zero = t1 at *
    cases htr
    <;> ctree_elim hz
    exact IsTraceOf.empty

  theorem IsTraceOf.map_ret {t : CTree ε ρ} (h : t.IsTraceOf (.ret x)) : (f <$> t).IsTraceOf (.ret <| f x) := by
    generalize htr : (Trace.ret x) = tr at *
    induction h with
    | empty =>
      contradiction
    | vis_end =>
      contradiction
    | vis_continue =>
      contradiction
    | ret =>
      simp only [Functor.map, CTree.map_ret, (Trace.ret.inj htr).symm]
      exact IsTraceOf.ret <| f x
    | tau _ _ ih =>
      simp only [Functor.map, CTree.map_tau]
      apply IsTraceOf.tau
      simp only [Functor.map] at ih
      exact ih htr
    | choice_left _ _ ih =>
      simp only [Functor.map, CTree.map_choice]
      apply IsTraceOf.choice_left
      simp only [Functor.map] at ih
      exact ih htr
    | choice_right _ _ ih =>
      simp only [Functor.map, CTree.map_choice]
      apply IsTraceOf.choice_right
      simp only [Functor.map] at ih
      exact ih htr

  theorem TraceRefine.dest_tau_right {t1 t2 : CTree ε ρ} (h : t1 ⊑ t2.tau) : t1 ⊑ t2 := by
    intro tr htr
    have := h tr htr
    generalize ht2 : t2.tau = t2t at *
    cases this
    <;> ctree_elim ht2
    case empty => exact .empty
    case tau h' =>
      rw [tau_inj ht2]
      exact h'

end CTree
