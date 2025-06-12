import CTree.Euttc
import CTree.LTS

namespace CTree

  theorem IsWeakSimulation.refine_of_val {t : CTree ε ρ}
    (h_lts_sim : IsWeakSimulation ltsSim)
    (h_ret : ltsSim (ret v) t)
    : RefineF Eq sim 0 0 (ret v) t := by
    obtain ⟨t2, tt, t2t, n1, n2, htau1, hs, htau2⟩ := h_lts_sim _ _ h_ret (.val v) zero .ret
    generalize hlv : Label.val v = lv at *
    induction hs with
    | vis => contradiction
    | tau => contradiction
    | ret =>
      have := Label.val.inj hlv
      subst this
      clear *- htau1
      revert t
      induction n1 with
      | zero =>
        intro t h
        simp only [NTauStep] at h
        subst h
        exact RefineF.ret rfl
      | succ n ih =>
        intro t htau1
        simp only [NTauStep] at htau1
        obtain ⟨t2, htau, htau1⟩ := htau1
        have := ih htau1
        clear *- this htau
        generalize hl : Label.tau = l at *
        induction htau with
        | ret => contradiction
        | vis => contradiction
        | tau =>
          apply RefineF.tau_right
          exact RefineF.idx_mono_right bot_le this
        | choice_left _ ih =>
          have := ih this hl
          apply RefineF.choice_left
          exact RefineF.idx_mono_right bot_le this
        | choice_right _ ih =>
          have := ih this hl
          apply RefineF.choice_right
          exact RefineF.idx_mono_right bot_le this
    | choice_left _ ih =>

      sorry
    | choice_right => sorry

  theorem refine_of_weak_simulation (h_sim : IsWeakSimulation sim) (h : sim t1 t2)
    : t1 ≤Eq≤ t2 := by
    apply Refine.coind (λ p1 p2 t1 t2 => sim t1 t2) _ 0 0 h
    intro p1 p2 t1 t2 h
    have h_step := h_sim _ _ h
    apply dMatchOn t1
    · intro v heq
      subst heq
      exact RefineF.idx_mono bot_le bot_le (h_sim.refine_of_val h)
    · sorry
    · sorry
    · sorry
    · sorry

  theorem euttc_of_lts {t1 t2 : CTree ε ρ} (h : WeakBisim t1 t2) : t1 ≈ t2 := by
    simp [WeakBisim] at h
    obtain ⟨sim, ⟨h1, h2⟩, h⟩ := h
    apply And.intro
    · have := h1 _ _ h

      sorry
    · sorry

end CTree
