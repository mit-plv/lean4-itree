import CTree.Par

namespace CTree
  macro "crush_parAux_eq" : tactic => `(tactic|(
    try rw [parAux_eq_def, parAux_def]
    try rw [parAux_eq_def, parAux_def]
    try congr
    try rw [parAux_eq_def, parAux_def]
    try rw [parAux_eq_def, parAux_def]
    try congr
    try rw [parAux_eq_def, parAux_def]
    try congr
  ))

  theorem parAux_parS_ret_tau {v : α} {t : CTree ε β}
    : parAux (ret v ‖ₛ t.tau)
      = (parAux (ParState.bothS (ret v) t)).tau
        ⊕ zero
        ⊕ (parAux (ParState.rS (ret v) t)).tau := by
    crush_parAux_eq

  theorem parAux_parS_ret_ret : parAux (ret (ε := ε) x ‖ₛ ret y) = ret (x, y) ⊕ (zero ⊕ zero) := by
    crush_parAux_eq

  theorem parAux_parS_ret_vis
    : parAux (ret (ε := ε) x ‖ₛ vis e k) = zero ⊕ (zero ⊕ vis e (fun a => parAux <| ret x ‖ₛ k a)) := by
    crush_parAux_eq

  theorem parAux_parS_ret_zero
    : parAux (ret (ε := ε) x ‖ₛ zero (ρ := β)) = zero ⊕ (zero ⊕ zero) := by
    crush_parAux_eq

  theorem parAux_parS_ret_choice
    : parAux (ret (ε := ε) x ‖ₛ c1 ⊕ c2)
      = (parAux (ret x ⋈ c1) ⊕ parAux (ret x ⋈ c2))
        ⊕ (zero ⊕ (parAux (ret x ▷ c1) ⊕ parAux (ret x ▷ c2))) := by
    crush_parAux_eq

  theorem parAux_parS_ret : parAux (ret (ε := ε) x ‖ₛ t) = parAux (ret x ⋈ t) ⊕ zero ⊕ parAux (ret x ▷ t) := by
    crush_parAux_eq

  theorem parAux_lS_ret : parAux (ret (ε := ε) x ◁ t) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_ret : parAux (ret (ε := ε) x ▷ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_tau : parAux (ret (ε := ε) x ▷ tau t) = (parAux (ret (ε := ε) x ▷ t)).tau := by
    rw [parAux_eq_def, parAux_def]
    congr

  theorem parAux_rS_ret_zero : parAux (ret (ε := ε) x ▷ zero (ρ := β)) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_choice : parAux (ret (ε := ε) x ▷ c1 ⊕ c2) = parAux (ret x ▷ c1) ⊕ parAux (ret x ▷ c2) := by
    rw [parAux_eq_def, parAux_def]
    congr

  theorem parAux_rS_ret_vis : parAux (ret x ▷ vis e k) = vis e λ a => parAux (ret x ‖ₛ k a) := by
    crush_parAux_eq

  theorem parAux_lrS : parAux (t1 ◁▷ t2) = parAux (t1 ◁ t2) ⊕ parAux (t1 ▷ t2) := by
    crush_parAux_eq

  theorem parAux_bothS_ret_ret : parAux (ret (ε := ε) x ⋈ ret y) = ret (x, y) := by
    crush_parAux_eq

  theorem parAux_bothS_ret_tau : parAux (ret (ε := ε) x ⋈ tau t) = (parAux (ret x ⋈ t)).tau := by
    rw [parAux_eq_def, parAux_def]
    congr

  theorem parAux_bothS_ret_vis : parAux (ret (ε := ε) x ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_zero : parAux (ret (ε := ε) x ⋈ zero (ρ := β)) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_choice : parAux (ret (ε := ε) x ⋈ c1 ⊕ c2) = parAux (ret x ⋈ c1) ⊕ parAux (ret x ⋈ c2) := by
    rw [parAux_eq_def, parAux_def]
    congr

  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (t1 ◁ t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (t1 ▷ t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (t1 ◁▷ t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (t1 ⋈ t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (t1 ‖ₛ t2)) → IsParR t t1 t2

  namespace Euttc
    macro "crush_refine" : tactic => `(tactic|(
      repeat first
      | exact RefineF.ret rfl
      | exact RefineF.zero
      | apply RefineF.tau_left
      | apply RefineF.tau_right
      | apply RefineF.vis
      | apply RefineF.choice_idemp
      | apply RefineF.choice_idemp
      | apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
    ))

    macro "crush_parR_ret " c:term : tactic => `(tactic|(
      repeat apply And.intro rfl _
      exists $c
      apply And.intro _ rfl
      solve
      | exact IsParR.bothS rfl
      | exact IsParR.rS rfl
      | exact IsParR.parS rfl
    ))

    macro "parR_ret_left_lS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      all_goals
        intros; rename_i heq; subst heq
        simp only [parAux_lS_ret, map_zero]
        crush_refine
    ))

    macro "parR_ret_left_rS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      · intro y heq
        subst heq
        simp only [parAux_rS_ret_ret, map_zero]
        crush_refine
      · intro c heq
        subst heq
        simp only [parAux_rS_ret_tau, map_tau]
        crush_refine; crush_parR_ret c
      · intro α e k heq
        subst heq
        simp only [parAux_rS_ret_vis, map_vis]
        crush_refine; intro a
        crush_refine; crush_parR_ret k a
      · intro heq
        subst heq
        simp only [parAux_rS_ret_zero, map_zero]
        crush_refine
      · intro c1 c2 heq
        subst heq
        simp only [parAux_rS_ret_choice, map_choice]
        crush_refine
        · apply RefineF.choice_left
          crush_refine; crush_parR_ret c1
        · apply RefineF.choice_right
          crush_refine; crush_parR_ret c2
    ))

    theorem parR_ret_le : ((ret x) ‖→ t) ≤Eq≤ t := by
      apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, IsParR t1 (ret x) t ∧ t2 = t) _ 0 0
      · crush_parR_ret t
      · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
        subst hp1 hp2 ht2
        match ht1 with
        | .lS heq =>
          subst heq
          parR_ret_left_lS t2
        | .rS heq =>
          subst heq
          parR_ret_left_rS t2
        | .lrS heq =>
          subst heq
          simp only [parAux_lrS, map_choice]
          apply RefineF.choice_idemp
          · parR_ret_left_lS t2
          · parR_ret_left_rS t2
        | .bothS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_bothS_ret_ret, map_ret]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_bothS_ret_tau, map_tau]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_bothS_ret_vis, map_zero]
            crush_refine
          · intro heq
            subst heq
            simp only [parAux_bothS_ret_zero, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_bothS_ret_choice, map_choice]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
        | .parS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_parS_ret_ret, map_choice, map_ret, map_zero]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_parS_ret_tau, map_choice, map_tau, map_zero]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_parS_ret_vis, map_choice, map_zero, map_vis]
            crush_refine
            intro a
            crush_refine; crush_parR_ret k a
          · intro heq
            subst heq
            simp only [parAux_parS_ret_zero, map_choice, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_parS_ret_choice, map_choice, map_zero]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
            · crush_refine
              · apply RefineF.choice_left
                crush_refine; crush_parR_ret c1
              · apply RefineF.choice_right
                crush_refine; crush_parR_ret c2

    theorem le_parR_ret : t ≤Eq≤ ((ret x) ‖→ t) := by
      apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, t2 = map Prod.snd (parAux (.bothS (ret x) t) ⊕ zero ⊕ parAux (.rS (ret x) t)) ∧ t1 = t) _ 0 0
      · repeat apply And.intro rfl _
        exists t
        apply And.intro _ rfl
        rw [parR, par, parAux_parS_ret]
        rfl
      · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
        subst hp1 hp2 ht1 ht2
        apply dMatchOn t1
        · intro y heq
          subst heq
          simp only [parAux_bothS_ret_ret, map_choice, map_ret]
          apply RefineF.choice_left
          crush_refine
        · intro c heq
          subst heq
          simp only [parAux_bothS_ret_tau, parAux_rS_ret_tau, map_choice, map_tau]
          sorry
        · sorry
        · sorry
        · sorry

    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · exact parR_ret_le
      · rw [flip_eq]
        exact le_parR_ret

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      simp only [parR, par, Functor.map]
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
