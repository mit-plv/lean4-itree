import CTree.LTS
import CTree.RefineSimLemmas

namespace CTree

  theorem refine_of_weak_sim_ret
    (hsim : IsWeakSimulation sim) (h : sim (C[ ret v ]) (C[ t2 ]))
    : ret v ≤ t2 := by
    simp only [LE.le, Refine, Refine']
    obtain ⟨t2', hws, hcont⟩ := hsim _ _ h (.val v) (C[ zero ]) .ret
    exists 0, 0
    exact RefineF.ret_of_weak_step hws

  theorem refine_of_weak_sim_vis {ε : Type → Type} {ρ : Type} {sim : Rel (State ε ρ) (State ε ρ)}
    {α : Type} {e : ε α} {t2 : CTree ε ρ} {k : KTree ε α ρ}
    (hsim : IsWeakSimulation sim) (h : sim (C[ vis e k ]) (C[ t2 ]))
    : RefineF Eq (λ _ _ t1 t2 => sim (C[ t1 ]) (C[ t2 ])) p1 p2 (vis e k) t2 := by
    ctree_match 2, t2
    case ret =>
      obtain ⟨t2, hws, h⟩ := hsim _ _ h (.event α e) (K[ k ]) .event
      exfalso; exact hws.ret_event
    case vis =>
      obtain ⟨sk2, hws, h⟩ := hsim _ _ h (.event α e) (K[ k ]) .event
      have := hsim _ _ h
      match sk2 with
      | C[ _ ] => contradiction
      | K[ α2 | _ ] =>
        obtain ⟨hα, hk⟩ := this
        subst hα
        simp_all only
        have hα := hws.vis_event_α.symm
        subst hα
        have he := hws.vis_event_e.symm
        subst he
        have ⟨_, hkeq⟩ := State.kt.inj hws.vis_event.symm
        subst hkeq
        exact RefineF.vis (p1' := 0) (p2' := 0) hk
    case tau =>
      obtain ⟨t2', hws, h⟩ := hsim _ _ h (.event α e) (K[ k ]) .event
      apply RefineF.tau_right
      have hws := hws.dest_tau_left
      simp only at hws
      exact RefineF.of_WeakStep_event hsim h hws
    case zero =>
      have ⟨_, hs, _⟩ := hsim _ _ h (.event α e) (K[ k ]) .event
      exfalso; exact hs.elim_zero
    case choice =>
      have ⟨st2, hws, h⟩ := hsim _ _ h (.event α e) (K[ k ]) .event
      have ⟨k2, hk2⟩ := hws.event_kt_right
      subst hk2
      apply hws.inv_choice_left.elim
      · intro hws
        apply RefineF.choice_left
        exact RefineF.of_WeakStep_event hsim h hws
      · intro hws
        apply RefineF.choice_right
        exact RefineF.of_WeakStep_event hsim h hws

  theorem weak_sim_of_refine : IsWeakSimulation (@RefineS ρ ρ ε Eq) := by
    intro t1 t2 href
    match t1, t2 with
    | C[ t1 ], C[ t2 ] =>
      intro l t1' hs
      split
      · obtain ⟨t1', ht1'⟩ := hs.tau_ct_right
        subst ht1'
        obtain ⟨p1, p2, href⟩ := href
        have := refine_tau_correspondence href t1' hs
        exists 0, C[ t2 ]
        apply And.intro rfl
        exists p1, p2
      · cases l with
        | tau => contradiction
        | val v =>
          have hz := Step.zero_of_val hs
          subst hz
          obtain ⟨_, _, href⟩ := href
          have := refine_ret_correspondence href hs
          have := weak_step_of_refine_ret this
          exists C[ zero ]
          exact And.intro this Refine.zero_le
        | event =>
          have ⟨k, hk⟩ := hs.event_kt_right
          subst hk
          obtain ⟨p1, p2, href⟩ := href
          have ⟨t2', hws, href⟩ := refine_event_correspondence href _ hs
          exists K[ t2' ]
          apply And.intro hws
          exists p1, p2, rfl
        | response =>
          obtain ⟨_, heq⟩ := hs.response_kt_left
          contradiction
    | K[ α | k1 ], K[ α2 | k2 ] =>
      obtain ⟨p1, p2, ⟨hα, hk⟩⟩ := href
      exists hα
      subst hα
      intro a
      exists p1, p2
      exact hk a
    | C[ _ ], K[ _ ] | K[ _ ], C[ _ ] =>
      obtain ⟨_, _, h⟩ := href
      exact h

end CTree
