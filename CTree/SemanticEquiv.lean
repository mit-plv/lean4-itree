import CTree.Euttc
import CTree.LTS
import CTree.ParLemmas
import CTree.RefineSimLemmas

namespace CTree

  theorem refine_of_weak_sim {sim : Rel (CTree ε ρ) (CTree ε ρ)} {t1 t2 : CTree ε ρ}
    (hsim : IsWeakSimulation sim) (h : sim t1 t2)
    : t1 ≤Eq≤ t2 := by
    apply Refine.coind (λ p1 p2 t1 t2 => sim t1 t2) _ 0 0 h
    intro p1 p2 t1 t2 h
    apply dMatchOn t1
    · intro x heq
      subst heq
      apply dMatchOn t2
      · intro y heq
        subst heq
        have := hsim (ret x) (ret y) h (.val x) zero .ret
        simp only at this
        obtain ⟨t2', hws, h⟩ := this
        apply RefineF.ret
        symm
        exact hws.ret_val
      · intro c heq
        subst heq
        sorry
      · sorry
      · sorry
      · sorry
    · sorry
    · sorry
    · sorry
    · sorry

  theorem weak_sim_of_refine : IsWeakSimulation (Refine Eq (ρ := ρ) (ε := ε)) := by
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

end CTree
