
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

infixr:67 " :: " => HList.cons
notation "[" "]" => HList.nil

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

namespace HList

  def get : HList β is → Member i is → β i
    | a :: as, .head => a
    | _ :: as, .tail h => as.get h

  def append : HList β is1 → HList β is2 → HList β (is1 ++ is2)
    | [], l => l
    | (h :: s), t => h :: s.append t

  infixr:67 " ++ " => HList.append

  -- Given a List α, a function f : α → β,
  -- return a HList with indices of type β and values of β-indexed type γ
  -- using the mapping function g : (a : α) → γ (f a).
  def from_list {α : Type v1} {β : Type v2} {δ : β → Type u}
                (f : α → β) (g : (a : α) → δ (f a)) : 
                (l : List α) → HList δ (l.map f)
    | [] => []
    | h :: t => g h :: from_list f g t

end HList