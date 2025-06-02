import CTree.Basic

namespace CTree
  @[aesop safe [constructors, cases]]
  inductive Trace (ε : Type → Type) (ρ : Type)
  | nil : Trace ε ρ
  | ret (v : ρ) : Trace ε ρ
  | event_end {α} (e : ε α) : Trace ε ρ
  | event_response {α} (e : ε α) (a : α) (cont : Trace ε ρ) : Trace ε ρ

  @[aesop safe [constructors, cases]]
  inductive IsTraceOf {ε : Type → Type} {ρ : Type} : Rel (CTree ε ρ) (Trace ε ρ)
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

  instance instCTreeLE : LE (CTree ε ρ) where
    le := TraceRefine

  theorem TraceRefine.ret_le {t : CTree ε ρ} (h : .ret v ≤ t) : t.IsTraceOf (.ret v) := by
    exact h (.ret v) (.ret v)

  theorem TraceRefine.ret_le_choice {t1 t2 : CTree ε ρ} (h : .ret v ≤ t1 ⊕ t2) : t1.IsTraceOf (.ret v) ∨ t2.IsTraceOf (.ret v) := by
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

  theorem TraceRefine.choice_le {t1 t2 t3 : CTree ε ρ} (h : (t1 ⊕ t2) ≤ t3) : t1 ≤ t3 ∧ t2 ≤ t3 := by
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
  theorem TraceRefine.refl {t : CTree ε ρ} : t ≤ t := by
    intro tr h
    simp_all only

  @[trans]
  theorem TraceRefine.trans {t1 t2 t3 : CTree ε ρ} (h1 : t1 ≤ t2) (h2 : t2 ≤ t3) : t1 ≤ t3 := by
    intro tr htr
    induction htr with
    | empty => exact .empty
    | ret v =>
      have := h1 (.ret v) (.ret v)
      cases this
      case ret => exact ret_le h2
      case tau h1 => exact h2 (.ret v) (.tau _ h1)
      all_goals
       (apply h1.ret_le_choice.elim
        · intro h
          exact h2.choice_le.left (.ret v) h
        · intro h
          exact h2.choice_le.right (.ret v) h)
    | tau => sorry
    | vis_end => sorry
    | vis_continue => sorry
    | choice_left => sorry
    | choice_right => sorry

end CTree
