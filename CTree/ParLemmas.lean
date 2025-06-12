import CTree.Par

namespace CTree
  theorem par_ret_tau_eq {v : α} {t : CTree ε β}
    : ret v ‖ t.tau
      = (parAux (ParState.bothS (ret v) t)).tau
        ⊕ zero
        ⊕ (parAux (ParState.rS (ret v) t)).tau := by
    simp only [par]
    conv =>
      lhs
      rw [parAux_eq_def, parAux_def]
      rw [parAux_eq_def, parAux_def]
      arg 1; arg 2
      simp only [ret, mk, ret', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 1; arg 3
      simp only [tau, mk, tau', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 2
      rw [parAux_eq_def, parAux_def]
      arg 1
      rw [parAux_eq_def, parAux_def]
      simp only [ret, mk, ret', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 2; arg 2
      rw [parAux_eq_def, parAux_def]
      arg 2
      simp only [tau, mk, tau', PFunctor.M.dest_mk]
    simp only [_fin1Const, _fin0, Fin2.ofNat']

  namespace Euttc
    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · apply Refine.coind (λ p1 p2 t1 t2 => ∃ t, t1 = (ret x) ‖→ t ∧ t2 = t) _ ⊤ ⊤
        -- · repeat apply And.intro rfl
        · exists t
        · intro p1 p2 _ t h
          obtain ⟨_, ht1, ht2⟩ := h
          -- subst hp1
          -- subst hp2
          subst ht1
          subst ht2
          apply dMatchOn t
          · intro v heq
            subst heq
            simp only [parR, par_ret_ret_eq, Functor.map, map_choice, map_ret, map_zero]
            apply RefineF.choice_idemp
            · exact RefineF.ret rfl
            · apply RefineF.choice_idemp
              <;> exact RefineF.zero
          · intro c heq
            subst heq
            simp only [parR]
            rw [par_ret_tau_eq]
            
            sorry
          · sorry
          · sorry
          · sorry
      · sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
