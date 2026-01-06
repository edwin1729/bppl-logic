/-! The probabilistic programming language without the observe/score primitive.
As defined in Lilac.

Will need the subtly different types of objects (in the semantic domain) that variables that
variables can be interpreted to, to be defined, as certain types are allowed to be used in
connectives of Lilac.

Each of these variables (terms) will need to be interpreted under an environment.

Use `env` for the values and `ctx` for the types of these values.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
universe u v
-- Primitives
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

  infix:67 " :: " => HList.cons

  notation "[" "]" => HList.nil

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | a::as, .tail h => as.get h
