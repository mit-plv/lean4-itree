
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

end HList

-- Given a List α, a function f : α → β,
-- return a HList with indices of type β and values of β-indexed type δ
-- using the mapping function g : (a : α) → δ (f a).
def List.to_hlist {α : Type v1} {β : Type v2} {δ : β → Type u}
                  (f : α → β) (g : (a : α) → δ (f a))
                  : (l : List α) → HList δ (l.map f)
  | [] => []
  | h :: t => g h :: t.to_hlist f g
