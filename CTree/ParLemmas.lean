import CTree.Par

namespace CTree
  macro "parAux_parS_eq" : tactic => `(tactic|(
    rw [parAux_eq_def, parAux_def]
    rw [parAux_eq_def, parAux_def]
    congr
    rw [parAux_eq_def, parAux_def]
    rw [parAux_eq_def, parAux_def]
    congr
    rw [parAux_eq_def, parAux_def]
    congr
  ))

  theorem parAux_parS_ret_tau {v : α} {t : CTree ε β}
    : parAux (.parS (ret v) t.tau)
      = (parAux (ParState.bothS (ret v) t)).tau
        ⊕ zero
        ⊕ (parAux (ParState.rS (ret v) t)).tau := by
    parAux_parS_eq

  theorem parAux_parS_ret_ret : parAux (.parS (ret (ε := ε) x) (ret y)) = ret (x, y) ⊕ (zero ⊕ zero) := by
    parAux_parS_eq

  theorem parAux_parS_ret_vis
    : parAux (.parS (ret (ε := ε) x) (vis e k)) = zero ⊕ (zero ⊕ vis e (fun a => parAux <| .parS (ret x) (k a))) := by
    parAux_parS_eq

  theorem parAux_parS_ret_zero
    : parAux (.parS (ret (ε := ε) x) (zero (ρ := β))) = zero ⊕ (zero ⊕ zero) := by
    parAux_parS_eq

  theorem parAux_parS_ret_choice
    : parAux (.parS (ret (ε := ε) x) (c1 ⊕ c2))
      = (parAux (.bothS (ret x) c1) ⊕ parAux (.bothS (ret x) c2))
        ⊕ (zero ⊕ (parAux (.rS (ret x) c1) ⊕ parAux (.rS (ret x) c2))) := by
    parAux_parS_eq

  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (.lS t1 t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (.rS t1 t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (.lrS t1 t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (.bothS t1 t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (.parS t1 t2)) → IsParR t t1 t2

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

    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, IsParR t1 (ret x) t ∧ t2 = t) _ 0 0
        · repeat apply And.intro rfl _
          exists t
          apply And.intro _ rfl
          exact IsParR.parS rfl
        · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
          subst hp1 hp2 ht2
          match ht1 with
          | .lS heq =>
            subst heq
            -- apply RefineF.coind
            sorry
          | .rS heq => sorry
          | .lrS heq => sorry
          | .bothS heq => sorry
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
      · sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
