import CTree.Par

namespace CTree
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
            simp only [parR]
            sorry
            -- simp only [parR, par, parBoth_ret_ret, parLeft_ret_ret, parRight_ret_ret,
            --   Functor.map, map_choice, map_zero, map_ret]
            -- apply RefineF.choice_idemp
            -- · apply RefineF.choice_idemp
            --   <;> exact RefineF.zero
            -- · exact RefineF.ret rfl
          · intro c heq
            subst heq
            -- simp only [parR, par, parBoth_ret_tau]
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
