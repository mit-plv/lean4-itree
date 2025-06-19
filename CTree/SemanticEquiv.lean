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

  theorem refine_of_weak_simC {sim : Rel (State ε ρ) (State ε ρ)} {t1 t2 : CTree ε ρ}
    (hsim : IsWeakSimulation sim) (h : sim (C[ t1 ]) (C[ t2 ]))
    : t1 ≤ t2 := by
    apply Refine.coind (λ p1 p2 t1 t2 => sim (C[ t1 ]) (C[ t2 ])) _ 0 0 h
    intro p1 p2 t1 t2 h
    ctree_match t1
    case ret =>
      obtain ⟨t2', hws, hcont⟩ := hsim _ _ h (.val v) (C[ zero ]) .ret
      exact RefineF.ret_of_weak_step hws
    case vis =>
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
    case tau =>
      have ⟨n, t2', htaun, hsim⟩ := hsim _ _ h .tau (C[ t ]) .tau
      apply RefineF.tau_left
      induction n with
      | zero =>
        subst htaun
        
        sorry
      | succ n ih =>
        sorry
    case zero => exact RefineF.zero
    case choice =>
      sorry

  theorem refine_of_weak_simK {sim : Rel (State ε ρ) (State ε ρ)} {k1 : KTree ε α1 ρ}
    (hsim : IsWeakSimulation sim) (h : sim (K[ k1 ]) (K[ k2 ]))
    : k1 ≤ k2 := by
    intro a
    have ⟨hα, hk⟩ := hsim _ _ h
    exact refine_of_weak_simC hsim (hk a)

  theorem refine_of_weak_sim {sim : Rel (State ε ρ) (State ε ρ)} {t1 t2 : State ε ρ}
    (hsim : IsWeakSimulation sim) (h : sim t1 t2)
    : t1 ≤ t2 := by
    match t1, t2 with
    | C[ t1 ], C[ t2 ] => exact refine_of_weak_simC hsim h
    | K[ α | k1 ], K[ α2 | k2 ] =>
      have ⟨hα, _⟩ := hsim _ _ h
      subst hα
      have hk := refine_of_weak_simK hsim h
      exists 0, 0, rfl
      intro a
      simp only [LE.le, RefineS, Refine'S, Refine, Refine', RefineK] at *
      have ⟨_, _, hk⟩ := hk a
      exact RefineF.idx_irrelevance hk _ _
    | C[ _ ], K[ _ ] | K[ _ ], C[ _ ] =>
      exfalso
      exact hsim _ _ h

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

  theorem weak_sim_iff_refine {t1 t2 : State ε ρ} : WeakSim t1 t2 ↔ t1 ≤ t2 :=
    ⟨λ ⟨_, hsim, h⟩ => refine_of_weak_sim hsim h, λ href => ⟨RefineS Eq, weak_sim_of_refine, href⟩⟩

end CTree
