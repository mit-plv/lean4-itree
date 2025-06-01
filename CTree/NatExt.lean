import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.Nat.Lattice

/-- Extended Natural Numbers -/

inductive NatExt
| nat : Nat → NatExt
| inf
deriving DecidableEq

instance : Repr NatExt where
  reprPrec n _ :=
    match n with
    | .nat n => s!"{n}"
    | .inf => s!"∞"

instance instOfNatNatExt : OfNat NatExt n where
  ofNat := NatExt.nat n

@[match_pattern]
def NatExt.add : NatExt → NatExt → NatExt
| .nat x, .nat y => .nat (x + y)
| _, _ => .inf

instance instAddNatExt : Add NatExt where
  add := NatExt.add

def NatExt.mul : NatExt → NatExt → NatExt
| _, 0 => 0
| 0, _ => 0
| .nat x, .nat y => .nat (x * y)
| _, _ => .inf

instance instMulNatExt : Mul NatExt where
  mul := NatExt.mul

@[simp]
def NatExt.lt : NatExt → NatExt → Prop
| .nat x, .nat y => x < y
| .inf, _ => False
| .nat _, .inf => True

instance instLTNatExt : LT NatExt where
  lt := NatExt.lt

instance instDecLtNatext (x y : NatExt) : Decidable (LT.lt x y) :=
  match x, y with
  | .nat x, .nat y => Nat.decLt x y
  | .inf, _ => .isFalse λ p => by simp only [LT.lt, NatExt.lt] at p
  | .nat _, .inf => .isTrue <| by simp only [LT.lt, NatExt.lt]

@[simp]
def NatExt.le (x y : NatExt) : Prop :=
  x = y ∨ NatExt.lt x y

instance instLENatExt : LE NatExt where
  le := NatExt.le

def NatExt.compare (x y : NatExt) : Ordering :=
  if x = y then
    .eq
  else if x < y then
    .lt
  else
    .gt

@[simp]
def NatExt.min (x y : NatExt) : NatExt :=
  if x < y then x else y

instance instMinNatExt : Min NatExt where
  min := NatExt.min

@[simp]
def NatExt.max (x y : NatExt) : NatExt :=
  if x < y then y else x

instance instMaxNatExt : Max NatExt where
  max := NatExt.max

@[simp]
def NatExt.toNatSet (s : Set NatExt) : Set Nat :=
  λ n => nat n ∈ s

open Classical in
@[simp]
noncomputable def NatExt.sSup (s : Set NatExt) : NatExt :=
  if inf ∈ s ∨ ¬s.Finite then
    inf
  else
    nat <| SupSet.sSup <| NatExt.toNatSet s

noncomputable instance instSupSetNatExt : SupSet NatExt where
 sSup := NatExt.sSup

open Classical in
@[simp]
noncomputable def NatExt.sInf (s : Set NatExt) : NatExt :=
  if s = singleton inf then
    inf
  else
    nat <| InfSet.sInf <| NatExt.toNatSet s

noncomputable instance instInfSetNatExt : InfSet NatExt where
 sInf := NatExt.sInf

theorem NatExt.not_lt : ¬(NatExt.lt x y) ↔ x = y ∨ NatExt.lt y x := by
  simp_all only [lt]
  apply Iff.intro
  · intro a
    split
    next x x_1 x_2 y =>
      simp_all only [_root_.not_lt, nat.injEq]
      apply (Nat.lt_or_eq_of_le a).elim
      · intro a_1
        simp_all only [or_true]
      · intro a_1
        subst a_1
        simp_all only [le_refl, lt_self_iff_false, or_false]
    next x_1 x_2 =>
      simp_all only [or_false]
      split at a
      next x x_3 x_4 y heq => simp_all only [reduceCtorEq]
      next x x_3 => simp_all only [not_false_eq_true]
      next x x_3 a_1 heq => simp_all only
    next x x_1 a_1 => simp_all only [not_false_eq_true, reduceCtorEq, or_true]
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    cases a with
    | inl h =>
      subst h
      split at a_1
      next x x_1 x_2 => simp_all only [lt_self_iff_false]
      next x x_1 => simp_all only
    | inr h_1 =>
      split at a_1
      next x x_1 x_2 y =>
        split at h_1
        next x_3 x_4 x_5 y_1 heq heq_1 =>
          simp_all only [nat.injEq]
          subst heq heq_1
          exact Nat.not_lt_of_lt a_1 h_1
        next x_3 x_4 heq => simp_all only [reduceCtorEq]
        next x_3 x_4 a heq heq_1 => simp_all only [nat.injEq, reduceCtorEq]
      next x x_1 =>
        split at h_1
        next x_2 x_3 x_4 y heq => simp_all only
        next x_2 x_3 => simp_all only
        next x_2 x_3 a heq => simp_all only
      next x x_1 a =>
        split at h_1
        next x_2 x_3 x_4 y heq heq_1 => simp_all only [reduceCtorEq]
        next x_2 x_3 heq => simp_all only
        next x_2 x_3 a_2 heq heq_1 => simp_all only [reduceCtorEq]

theorem NatExt.not_lt_inf : ¬(NatExt.lt x .inf) ↔ x = .inf := by
  simp_all only [lt]
  apply Iff.intro
  · intro a
    split at a
    next x x_1 x_2 y heq => simp_all only [reduceCtorEq]
    next x x_1 => simp_all only [not_false_eq_true]
    next x x_1 a_1 heq => simp_all only
  · intro a
    subst a
    simp_all only [not_false_eq_true]

@[simp]
theorem NatExt.inf_lt (h : NatExt.lt .inf x) : x = .inf := by
  simp_all only [lt]

@[simp]
theorem NatExt.nat_lt (h : NatExt.lt (.nat x) (.nat y)) : x < y := by
  simp_all only [lt]

instance instBotNat : Bot NatExt where
  bot := 0

instance instTopNat : Top NatExt where
  top := .inf

@[refl]
theorem NatExt.le_refl : NatExt.le x x := by
  simp only [le, true_or]

@[trans]
theorem NatExt.lt_trans (h1 : NatExt.lt x y) (h2 : NatExt.lt y z) : NatExt.lt x z := by
  simp_all only [lt]
  split
  next x x_1 x_2 y_1 =>
    split at h1
    next x_3 x_4 x_5 y heq =>
      split at h2
      next x_6 x_7 x_8 y_2 heq_1 heq_2 =>
        simp_all only [nat.injEq]
        subst heq_1 heq heq_2
        trans <;> assumption
      next x_6 x_7 heq_1 => simp_all only [nat.injEq, reduceCtorEq]
      next x_6 x_7 a heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
    next x_3 x_4 x_5 heq =>
      split at h2
      next x_3 x_6 x_7 y heq_1 => simp_all only [reduceCtorEq]
      next x_3 x_6 => simp_all only [reduceCtorEq]
      next x_3 x_6 a heq_1 => simp_all only [reduceCtorEq]
    next x_3 x_4 a heq =>
      split at h2
      next x_5 x_6 x_7 y heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
      next x_5 x_6 heq_1 => simp_all only [nat.injEq]
      next x_5 x_6 a_1 heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
  next x x_1 => simp_all only
  next x x_1 a => simp_all only

@[trans]
theorem NatExt.le_trans (h1 : NatExt.le x y) (h2 : NatExt.le y z) : NatExt.le x z := by
  simp_all only [le, lt]
  cases h1 with
  | inl h =>
    cases h2 with
    | inl h_1 =>
      subst h_1 h
      simp_all only [true_or]
    | inr h_2 =>
      subst h
      simp_all only [or_true]
  | inr h_1 =>
    cases h2 with
    | inl h =>
      subst h
      simp_all only [or_true]
    | inr h_2 =>
      split
      next x x_1 x_2 y_1 =>
        simp_all only [nat.injEq]
        split at h_1
        next x_3 x_4 x_5 y heq =>
          split at h_2
          next x_6 x_7 x_8 y_2 heq_1 heq_2 =>
            simp_all only [nat.injEq]
            subst heq heq_2 heq_1
            apply Or.inr
            trans <;> assumption
          next x_6 x_7 heq_1 => simp_all only [nat.injEq, reduceCtorEq]
          next x_6 x_7 a heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
        next x_3 x_4 x_5 heq =>
          split at h_2
          next x_3 x_6 x_7 y heq_1 => simp_all only [reduceCtorEq]
          next x_3 x_6 => simp_all only [reduceCtorEq]
          next x_3 x_6 a heq_1 => simp_all only [reduceCtorEq]
        next x_3 x_4 a heq =>
          split at h_2
          next x_5 x_6 x_7 y heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
          next x_5 x_6 heq_1 => simp_all only [nat.injEq]
          next x_5 x_6 a_1 heq_1 heq_2 => simp_all only [nat.injEq, reduceCtorEq]
      next x x_1 => simp_all only
      next x x_1 a => simp_all only [reduceCtorEq, or_true]

theorem NatExt.le_antisymm : NatExt.le x y → NatExt.le y x → x = y := by
  intro a a_1
  simp_all only [le, lt]
  cases a with
  | inl h =>
    cases a_1 with
    | inl h_1 =>
      subst h_1
      simp_all only
    | inr h_2 =>
      subst h
      simp_all only
  | inr h_1 =>
    cases a_1 with
    | inl h =>
      subst h
      simp_all only
    | inr h_2 =>
      split at h_1
      next x x_1 x_2 y =>
        split at h_2
        next x_3 x_4 x_5 y_1 heq heq_1 =>
          simp_all only [nat.injEq]
          subst heq_1 heq
          exact Nat.le_antisymm (Nat.le_of_lt h_1) (Nat.le_of_lt h_2)
        next x_3 x_4 heq => simp_all only [reduceCtorEq]
        next x_3 x_4 a heq heq_1 => simp_all only [nat.injEq, reduceCtorEq]
      next x x_1 =>
        split at h_2
        next x_2 x_3 x_4 y heq => simp_all only
        next x_2 x_3 => simp_all only
        next x_2 x_3 a heq => simp_all only
      next x x_1 a =>
        split at h_2
        next x_2 x_3 x_4 y heq heq_1 => simp_all only [reduceCtorEq]
        next x_2 x_3 heq => simp_all only
        next x_2 x_3 a_1 heq heq_1 => simp_all only [reduceCtorEq]

theorem NatExt.le_sup_left {x y : NatExt} : NatExt.le x (x.max y) := by
  simp_all only [le, NatExt.max, lt]
  split
  next h =>
    split
    next x x_1 x_2 y =>
      simp_all only [nat.injEq]
      apply Or.inr
      exact NatExt.nat_lt h
    next x x_1 =>
      simp_all only [or_false]
      rw [NatExt.inf_lt h]
    next x x_1 a => simp_all only [reduceCtorEq, or_true]
  next h => simp_all only [true_or]

theorem NatExt.le_sup_right {x y : NatExt} : NatExt.le y (x.max y) := by
  simp_all only [le, NatExt.max, lt]
  split
  next h => simp_all only [true_or]
  next h =>
    split
    next x x_1 x_2 y =>
      simp_all only [nat.injEq]
      apply (NatExt.not_lt.mp h).elim
      · intro a
        simp_all only [nat.injEq, lt_self_iff_false, or_false]
      · intro a
        simp_all only [lt, or_true]
    next x_1 x_2 =>
      simp_all only [or_false]
      exact (NatExt.not_lt_inf.mp h).symm
    next x x_1 a => simp_all only [reduceCtorEq, or_true]

theorem NatExt.sup_le (h1 : NatExt.le x z) (h2 : NatExt.le y z) : (x.max y).le z := by
  simp_all only [le, lt, NatExt.max]
  cases h1 with
  | inl h =>
    cases h2 with
    | inl h_1 =>
      subst h_1 h
      simp_all only [ite_self, true_or]
    | inr h_2 =>
      subst h
      simp_all only [ite_eq_right_iff]
      split
      next x x_1 x_2 y_1 heq =>
        split at h_2
        next x_3 x_4 x_5 y heq_1 =>
          split at heq
          next h => simp_all only [nat.injEq, forall_const, or_true]
          next h => simp_all only [nat.injEq, lt, inf_lt, implies_true, lt_self_iff_false, or_false]
        next x_3 x_4 =>
          split at heq
          next h => simp_all only
          next h => simp_all only
        next x_3 x_4 a heq_1 =>
          split at heq
          next h => simp_all only [reduceCtorEq]
          next h => simp_all only [reduceCtorEq]
      next x x_1 x_2 heq =>
        simp_all only [or_false]
        intro a
        simp_all only [↓reduceIte]
      next x x_1 a heq => simp_all only [or_true]
  | inr h_1 =>
    cases h2 with
    | inl h =>
      subst h
      simp_all only [ite_eq_left_iff]
      split
      next x_1 x_2 x_3 y heq =>
        split at h_1
        next x x_4 x_5 y_1 heq_1 =>
          split at heq
          next h =>
            simp_all only [nat.injEq, not_true_eq_false, lt, inf_lt, implies_true, lt_self_iff_false, or_false]
          next h => simp_all only [nat.injEq, not_false_eq_true, forall_const, or_true]
        next x x_4 =>
          split at heq
          next h => simp_all only
          next h => simp_all only
        next x x_4 a heq_1 =>
          split at heq
          next h => simp_all only [reduceCtorEq]
          next h => simp_all only [reduceCtorEq]
      next x_1 x_2 x_3 heq =>
        simp_all only [or_false]
        intro a
        simp_all only [↓reduceIte]
      next x_1 x_2 a heq => simp_all only [or_true]
    | inr h_2 =>
      split
      next h => simp_all only [or_true]
      next h => simp_all only [or_true]

theorem NatExt.inf_le_left {x y : NatExt} : (x.min y).le x := by
  simp_all only [le, NatExt.min, ite_eq_left_iff, lt]
  split
  next x x_1 x_2 y_1 heq =>
    split at heq
    next h => simp_all only [nat.injEq, not_true_eq_false, lt, inf_lt, implies_true, lt_self_iff_false, or_false]
    next h =>
      subst heq
      simp_all only [not_false_eq_true, nat.injEq, forall_const]
      apply (NatExt.not_lt.mp h).elim
      · intro a
        simp_all only [nat.injEq, lt_self_iff_false, or_false]
      · intro a
        simp_all only [lt, or_true]
  next x x_1 x_2 heq =>
    simp_all only [or_false]
    intro a
    simp_all only [↓reduceIte]
    subst heq
    exact (NatExt.not_lt_inf.mp a).symm
  next x x_1 a heq =>
    subst heq
    simp_all only [reduceCtorEq, imp_false, Decidable.not_not, or_true]

theorem NatExt.inf_le_right {x y : NatExt} : (x.min y).le y := by
  simp_all only [le, NatExt.min, ite_eq_right_iff, lt]
  split
  next x_1 x_2 x_3 y heq =>
    split at heq
    next h =>
      subst heq
      simp_all only [nat.injEq, forall_const]
      exact Or.inr <| NatExt.nat_lt h
    next h => simp_all only [nat.injEq, lt, inf_lt, implies_true, lt_self_iff_false, or_false]
  next x_1 x_2 x_3 heq =>
    simp_all only [or_false]
    intro a
    simp_all only [↓reduceIte]
    subst heq
    exact (NatExt.inf_lt a).symm
  next x_1 x_2 a heq => simp_all only [or_true]

theorem NatExt.le_inf {x y z : NatExt} (h1 : x.le y) (h2 : x.le z) : x.le (y.min z) := by
  simp_all only [le, lt, NatExt.min]
  cases h1 with
  | inl h =>
    cases h2 with
    | inl h_1 =>
      subst h h_1
      simp_all only [ite_self, true_or]
    | inr h_2 =>
      subst h
      split
      next h => simp_all only [true_or]
      next h => simp_all only [or_true]
  | inr h_1 =>
    cases h2 with
    | inl h =>
      subst h
      split
      next h => simp_all only [or_true]
      next h => simp_all only [true_or]
    | inr h_2 =>
      split
      next h => simp_all only [or_true]
      next h => simp_all only [or_true]

theorem NatExt.memNatSet_of_mem_set {s : Set NatExt} (h : nat x ∈ s) : x ∈ toNatSet s := by
  exact h

theorem NatExt.lt_iff_le_not_le {a b : NatExt} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  sorry

theorem NatExt.ne_inf (h : x ≠ NatExt.inf) : ∃ n, x = nat n := by
  cases x
  simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, nat.injEq, exists_eq']
  simp_all only [ne_eq, not_true_eq_false]

theorem NatExt.mem_not_inf {x : NatExt} {s : Set NatExt} (hinf : inf ∉ s) (h : x ∈ s) : ∃ n : Nat, x = nat n := by
  apply NatExt.ne_inf
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [not_true_eq_false]

theorem NatExt.toNatSet_finite {s : Set NatExt} (hinf : inf ∉ s) (h : s.Finite) : (NatExt.toNatSet s).Finite := by
  unfold NatExt.toNatSet
  obtain ⟨toFun, invFun, left_inverse, right_inverse⟩ := h
  rename_i n
  apply finite_iff_exists_equiv_fin.mpr
  exists n
  apply Nonempty.intro
  apply Equiv.mk
    (λ ⟨x, hx⟩ => toFun ⟨nat x, hx⟩)
    (λ i =>
      let ⟨x, hx⟩ := invFun i
      match x with
      | .nat n => ⟨n, hx⟩
      | .inf => by simp_all only [not_true_eq_false]
    )
  · intro x
    simp_all only
    obtain ⟨val, property⟩ := x
    simp_all only
    split
    next x hx n_1 hx_1 heq heq_1 =>
      simp_all only [heq_eq_eq, Subtype.mk.injEq]
      have := Subtype.mk.inj (left_inverse ⟨nat val, property⟩)
      rw [this] at heq
      simp_all only [nat.injEq]
    next x hx hx_1 heq heq_1 =>
      simp_all only [heq_eq_eq]
      contradiction
  · intro x
    simp_all only
    split
    next x_1 hx n_1 hx_1 heq heq_1 =>
      simp_all only [heq_eq_eq]
      have := right_inverse x
      rw [←this]
      have : invFun x = ⟨nat n_1, (match nat n_1, hx_1 with
                                  | nat n, hx => Subtype.mk n hx
                                  | inf, hx => (Eq.mp (Eq.trans (congrArg Not (eq_true hx)) not_true_eq_false) hinf).elim).property⟩ := by
        ext : 1
        simp_all only
      rw [this]
    next x_1 hx hx_1 heq heq_1 =>
      simp_all only [heq_eq_eq]
      contradiction

@[simp]
theorem NatExt.le_infy {x : NatExt} : x ≤ inf := by
  simp only [LE.le, le, lt]
  by_cases h : x = inf
  · exact Or.inl h
  · apply Or.inr
    split
    next x x_1 x_2 y heq => simp_all only [reduceCtorEq]
    next x x_1 => simp_all only [not_true_eq_false]
    next x x_1 a heq => simp_all only [reduceCtorEq, not_false_eq_true]

theorem NatExt.le_directed {a b : NatExt} : ∃ c, a ≤ c ∧ b ≤ c := by
  exists inf
  simp_all only [le_infy, and_self]

instance instPreorderNatext : Preorder NatExt where
  le_refl := @NatExt.le_refl
  le_trans := @NatExt.le_trans
  lt_iff_le_not_le := @NatExt.lt_iff_le_not_le

instance instIsDirectedNatExtLE : IsDirected NatExt LE.le where
  directed := @NatExt.le_directed

@[simp]
theorem NatExt.nat_le_sSup {s : Set NatExt} (hinf : inf ∉ s) (hfin : s.Finite) (h : nat x ∈ s)
  : x ≤ SupSet.sSup (NatExt.toNatSet s) := by
  have := NatExt.memNatSet_of_mem_set h
  apply le_csSup _ this
  exact Set.Finite.bddAbove (NatExt.toNatSet_finite hinf hfin)

theorem NatExt.le_sSup {s : Set NatExt} : ∀ x ∈ s, x.le (sSup s) := by
  intro x a
  simp_all only [le, sSup, lt]
  split
  next h =>
    cases h with
    | inl h_1 =>
      split
      next x x_1 x_2 y heq => simp_all only [reduceCtorEq]
      next x x_1 => simp_all only [or_false]
      next x x_1 a_1 heq => simp_all only [reduceCtorEq, or_true]
    | inr h_2 =>
      split
      next x x_1 x_2 y heq => simp_all only [reduceCtorEq]
      next x x_1 => simp_all only [or_false]
      next x x_1 a_1 heq => simp_all only [reduceCtorEq, or_true]
  next h =>
    simp_all only [not_or, not_not]
    obtain ⟨left, right⟩ := h
    split
    next x x_1 x_2 y heq =>
      simp_all only [nat.injEq]
      subst heq
      have := NatExt.nat_le_sSup left right a
      exact (Nat.le_iff_lt_or_eq.mp this).symm
    next x x_1 => simp_all only [not_true_eq_false]
    next x x_1 a_1 heq => simp_all only [reduceCtorEq]

noncomputable instance instCompleteLinearOrderNatExt : CompleteLinearOrder NatExt where
  inf := NatExt.min
  sup := NatExt.max
  compare := NatExt.compare
  le_refl := @NatExt.le_refl
  le_trans := @NatExt.le_trans
  le_antisymm := @NatExt.le_antisymm
  le_sup_left := @NatExt.le_sup_left
  le_sup_right := @NatExt.le_sup_right
  sup_le _ _ _ := NatExt.sup_le
  inf_le_left := @NatExt.inf_le_left
  inf_le_right := @NatExt.inf_le_right
  le_inf := @NatExt.le_inf
  le_sSup := @NatExt.le_sSup
  sSup_le := sorry
  sInf_le := sorry
  le_sInf := sorry
  le_top := sorry
  bot_le := sorry
  himp := sorry
  le_himp_iff := sorry
  compl := sorry
  himp_bot := sorry
  sdiff := sorry
  hnot := sorry
  sdiff_le_iff := sorry
  top_sdiff := sorry
  le_total := sorry
  toDecidableLE := sorry
  lt_iff_le_not_le := @NatExt.lt_iff_le_not_le
  compare_eq_compareOfLessAndEq := sorry

noncomputable instance instCompleteLatticeNatExt : CompleteLattice NatExt :=
  instCompleteLinearOrderNatExt.toCompleteLattice
