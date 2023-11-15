
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

infixr:67 " :: " => HList.cons
notation "[" "]" => HList.nil

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def List.nth_member : (l : List α) → (n : Fin l.length) → Member (l.get n) l
  | _::_, ⟨0, _⟩ => .head
  | _::t, ⟨n'+1, _⟩ => .tail (t.nth_member ⟨n', _⟩)

namespace HList

  def length : HList β is → Nat
    | [] => 0
    | _ :: t => 1 + t.length

  def get : HList β is → Member i is → β i
    | a :: as, .head => a
    | _ :: as, .tail h => as.get h

  def get_nth : (l : HList β is) → (n : Fin is.length) → β (is.get n)
    | h :: _, ⟨0, _⟩ => h
    | _ :: t, ⟨n + 1, _⟩ => t.get_nth ⟨n, _⟩

  def append : HList β is1 → HList β is2 → HList β (is1 ++ is2)
    | [], l => l
    | (h :: s), t => h :: s.append t

  infixr:67 " ++ " => HList.append

  -- Given a List α, a function f : α → β,
  -- return a HList with indices of type β and values of β-indexed type δ
  -- using the mapping function g : (a : α) → δ (f a).
  def from_list {α : Type v1} {β : Type v2} {δ : β → Type u}
                (f : α → β) (g : (a : α) → δ (f a)) :
                (l : List α) → HList δ (l.map f)
    | [] => []
    | h :: t => g h :: from_list f g t

  -- Given a List α, a function f : α → β,
  -- return a HList with indices of type β and values of β-indexed type δ
  -- using the mapping function g : (a : α) → δ (f a).
  def from_list_with_mem {α : Type v1} {β : Type v2} {δ : β → Type u}
                        (l : List α) (f : α → β) (g : (a : α) → a ∈ l → δ (f a))
                        : HList δ (l.map f) :=
    match l with
      | [] => []
      | h :: t => g h (List.Mem.head t) :: from_list_with_mem t f (λ a h_mem => g a (List.Mem.tail h h_mem))

end HList


inductive Test
  | a : Nat → Test
  | b
  | c

def Test.is_a : Test → Bool
  | .a _ => true
  | _ => false

def f : (t : Test) → t.is_a = true → Nat
  | .a n, _ => n
