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

  theorem refine_of_weak_sim {sim : Rel (CTree ε ρ) (CTree ε ρ)} {t1 t2 : CTree ε ρ}
    (hsim : IsWeakSimulation sim) (h : sim t1 t2)
    : t1 ≤ t2 := by
    apply Refine.coind (λ p1 p2 t1 t2 => sim t1 t2) _ 0 0 h
    intro p1 p2 t1 t2 h
    ctree_match t1
    case ret =>
      obtain ⟨t2', hws, hcont⟩ := hsim (ret v) t2 h (.val v) zero .ret
      exact RefineF.ret_of_weak_step hws
    case vis =>
      ctree_match 2, t2
      case ret =>
        sorry
      case vis =>
        sorry
      case tau =>
        sorry
      case zero =>
        sorry
      case choice =>
        sorry
    case tau =>
      sorry
    case zero => exact RefineF.zero
    case choice =>
      sorry

  theorem weak_sim_of_refine : IsWeakSimulation (@Refine ρ ρ ε Eq) := by
    intro t1 t2 href l t1' hs
    obtain ⟨_, _, href⟩ := href
    split
    · have := refine_tau_correspondence href t1' hs
      exists 0, t2
      apply And.intro rfl
      rename_i p1 p2 _
      exists p1, p2
    · cases l with
      | tau => contradiction
      | val v =>
        have := Step.zero_of_val hs
        subst this
        have := refine_ret_correspondence href hs
        have := weak_step_of_refine_ret this
        exists zero
        exact And.intro this Refine.zero_le
      | event =>
        have ⟨t2', hws, href⟩ := refine_event_correspondence href _ hs
        exists t2'
        exact And.intro hws ⟨_, _, href⟩

  theorem weak_sim_iff_refine {t1 t2 : CTree ε ρ} : WeakSim t1 t2 ↔ t1 ≤ t2 :=
    ⟨λ ⟨_, hsim, h⟩ => refine_of_weak_sim hsim h, λ href => ⟨Refine Eq, weak_sim_of_refine, href⟩⟩

end CTree
