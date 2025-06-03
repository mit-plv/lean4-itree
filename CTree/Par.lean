import CTree.Basic
import CTree.Monad
import CTree.TraceEq

namespace CTree
  /- Paralle Opeartor -/

  def vis_left {α β} (par : CTree ε α → CTree ε β → CTree ε (α × β))
    (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  def bothRet (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  inductive ParFlag
  | visLeft
  | visRight
  | ret

  def choice3' (t1 t2 t3 : X) : P ε ρ (P ε ρ X) :=
    .mk .choice (_fin2Const sorry (.mk .choice (_fin2Const t2 t3)))

  def choice3 (t1 t2 t3 : CTree ε ρ) : CTree ε ρ :=
    t1 ⊕ t2 ⊕ t3

  -- TODO: How to do the case with two events?
  def biasedEffect (flag : ParFlag) (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    match flag with
    | .visLeft =>
      PFunctor.M.corec3 (λ rec ((flag, t1, t2) : ParFlag × CTree ε α × CTree ε β) =>
        match t1.dest with
        | ⟨.ret _, _⟩ => .res <| zero
        | ⟨.tau, c⟩ => .one <| tau' <| rec (.visLeft, c _fin0, t2)
        | ⟨.zero, _⟩ => .res zero
        | ⟨.choice, cts⟩ => .one <| choice' (rec (.visLeft, cts _fin0, t2)) (rec (.visLeft, cts _fin1, t2))
        | ⟨.vis _ e, k⟩ =>
          .two <| vis' e λ a =>
            let k := k (.up a)
            -- choice' (rec (.visLeft, k, t2), choice' (rec (.visLeft, k, t2)) (rec (.visRight, k, t2))) --(rec (.ret, k, t2))
            sorry
      ) (flag, t1, t2)
    | .visRight =>
      sorry
    | .ret =>
      sorry

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry
  infixr:60 " || " => par

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 || t2)
  infixr:60 " ||→ " => parR

  namespace TraceEq
    theorem parR_ret : ((ret x) ||→ t) ≈ t := by
      sorry

    theorem parR_map : ((map f t1) ||→ t2) ≈ (t1 ||→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ||→ t2) ||→ t3) ≈ (t1 ||→ (t2 ||→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ||→ t2) ||→ t3) ≈ ((t2 ||→ t1) ||→ t3) := by
      sorry
  end TraceEq

end CTree
