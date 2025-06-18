import CTree.Euttc
import CTree.LTS
import CTree.ParLemmas
import CTree.RefineSimLemmas

namespace CTree

  syntax "ctree_match " (num ", ")? term (" with " tactic)? : tactic
  open Lean in
  macro_rules
    | `(tactic|ctree_match $[$n:num,]? $t:term $[ with $simp_rule:tactic]?) => do
      let n := (n.map (Nat.repr ∘ TSyntax.getNat)).getD ""
      let mkIdent' (name : String) := mkIdent (.str .anonymous s!"{name}{n}")
      let simp_rule ←
        match simp_rule with
        | some simp_rule => `(tactic|(
            all_goals try ($simp_rule; crush_refine)
          ))
        | none => `(tactic|skip)
      `(tactic|(
        apply dMatchOn $t
        case' ret =>
          intro $(mkIdent' "v") heq
          subst heq
        case' vis =>
          intro $(mkIdent' "α") $(mkIdent' "e") $(mkIdent' "k") heq
          subst heq
        case' tau =>
          intro $(mkIdent' "t") heq
          subst heq
        case' zero =>
          intro heq
          subst heq
        case' choice =>
          intro $(mkIdent' "cl") $(mkIdent' "cr") heq
          subst heq
        $simp_rule
      ))

  theorem refine_of_weak_sim {sim : Rel (State ε ρ) (State ε ρ)} {t1 t2 : State ε ρ}
    (hsim : IsWeakSimulation sim) (h : sim t1 t2)
    : t1 ≤ t2 := by
    match t1 with
    | C[ t1 ] => sorry
    | K[ α | k1 ] =>
      if hemp : IsEmpty α then
        whnf
        exists 0, 0
        have := hsim _ _ h
        whnf
        -- We cannot produce an `a` to see what `t2` step to
        -- So we cannot even decide whether `t2` is a continuatoin
        sorry
      else
        simp only [not_isEmpty_iff] at hemp
        apply Nonempty.elim hemp
        intro a
        -- How do we make a `e` to pass to `Label.response`?
        -- have := hsim _ _ h (.response α e a)
        sorry
    -- apply Refine.coind (λ p1 p2 t1 t2 => sim t1 t2) _ 0 0 h
    -- intro p1 p2 t1 t2 h
    -- ctree_match t1
    -- case ret =>
    --   obtain ⟨t2', hws, hcont⟩ := hsim (ret v) t2 h (.val v) zero .ret
    --   exact RefineF.ret_of_weak_step hws
    -- case vis =>
    --   ctree_match 2, t2
    --   case ret =>
    --     sorry
    --   case vis =>
    --     sorry
    --   case tau =>
    --     sorry
    --   case zero =>
    --     sorry
    --   case choice =>
    --     sorry
    -- case tau =>
    --   sorry
    -- case zero => exact RefineF.zero
    -- case choice =>
    --   sorry

  theorem weak_sim_of_refine : IsWeakSimulation (@RefineS ρ ρ ε Eq) := by
    intro t1 t2 href l t1' hs
    obtain ⟨p1, p2, href⟩ := href
    split
    · obtain ⟨t1, ht1⟩ := hs.tau_ct_left
      obtain ⟨t1', ht1'⟩ := hs.tau_ct_right
      subst ht1 ht1'
      whnf at href
      split at href <;> try contradiction
      rename_i heq
      have heq := State.ct.inj heq
      subst heq
      have := refine_tau_correspondence href t1' hs
      rename_i t2
      exists 0, C[ t2 ]
      apply And.intro rfl
      exists p1, p2
    · cases l with
      | tau => contradiction
      | val v =>
        have := Step.zero_of_val hs
        subst this
        obtain ⟨t1, ht1⟩ := hs.val_ct_left
        subst ht1
        whnf at href
        split at href <;> try contradiction
        rename_i heq
        have heq := State.ct.inj heq
        subst heq
        have := refine_ret_correspondence href hs
        have := weak_step_of_refine_ret this
        exists C[ zero ]
        exact And.intro this Refine.zero_le
      | event =>
        have ⟨t1, ht1⟩ := hs.event_ct_left
        have ⟨k, hk⟩ := hs.event_kt_right
        subst ht1 hk
        whnf at href
        split at href <;> try contradiction
        rename_i heq
        have heq := State.ct.inj heq
        subst heq
        have ⟨t2', hws, href⟩ := refine_event_correspondence href _ hs
        exists K[ t2' ]
        apply And.intro hws
        exists p1, p2, rfl
      | response =>
        rename_i α e a _
        obtain ⟨k1, hk1⟩ := hs.response_kt_left
        subst hk1
        cases hs
        whnf at href
        split at href <;> try contradiction
        obtain ⟨hα, href⟩ := href
        subst hα
        simp_all only [imp_false, State.kt.injEq]
        rename_i heq
        obtain ⟨hα, hk⟩ := heq
        subst hα hk
        rename_i t1 t2
        exists C[ t2 a ]
        apply And.intro _ ⟨p1, p2, href a⟩
        exists K[ t2 ], C[ t2 a ], 0, 0
        apply And.intro
        · simp only [NTauStep]
        · apply And.intro .response
          simp only [NTauStep]

  theorem weak_sim_iff_refine {t1 t2 : State ε ρ} : WeakSim t1 t2 ↔ t1 ≤ t2 :=
    ⟨λ ⟨_, hsim, h⟩ => refine_of_weak_sim hsim h, λ href => ⟨RefineS Eq, weak_sim_of_refine, href⟩⟩

end CTree
