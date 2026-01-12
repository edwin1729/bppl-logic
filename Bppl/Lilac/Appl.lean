import Mathlib

/-! The probabilistic programming language without the observe/score primitive.
As defined in Lilac.

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
-- start with Ty

namespace Appl
-- Lilac A.1 and A.2 (appendix)
inductive Ty where
  | prod : Ty → Ty → Ty
  | bool
  | real
  | exp : ℕ → Ty → Ty -- Tyⁿ
  | index
  | G : Ty → Ty

scoped notation ty₁ " × " ty₂ => Ty.prod ty₁ ty₂

structure Arith where
  plus : Arith
  minus : Arith
  mult : Arith
  div : Arith
  exp : Arith

structure Cmp where
  lt : Cmp
  le : Cmp
  eq : Cmp

inductive Term : List Ty → Ty → Type
  | var : Member ty ctx → Term ctx ty
  | ret : Term ctx ty → Term ctx (.G ty)
  | bind : Term ctx (.G ty₁) → Term (ty₁ :: ctx) (.G ty₂) → Term ctx (.G ty₂)
  | pair  : Term ctx ty₁ → Term ctx ty₂ → Term ctx (ty₁ × ty₂)
  | fst : Term ctx (ty₁ × ty₂) → Term ctx ty₁
  | snd : Term ctx (ty₁ × ty₂) → Term ctx ty₂
  | T : Term ctx .bool
  | F : Term ctx .bool
  | ite : Term ctx .bool → Term ctx ty → Term ctx ty → Term ctx ty
  | flip : Set.Icc 0 1 → Term ctx (.G .bool)
  | r : ℝ → Term ctx .real
  | arith : Arith → Term ctx .real → Term ctx .real → Term ctx .real
  | cmp : Cmp → Term ctx .real → Term ctx .real → Term ctx .bool
  | unif01 : Term ctx (.G .real)
  | vect : (Fin n → Term ctx ty) → Term ctx (.exp n ty)
  | index : Term ctx .index → Term ctx (.exp n ty) → Term ctx ty
  -- No need to specify name for `i`: index and `X`: A, since we're using De brujin indices
  | for : ℕ → Term ctx ty → Term (index :: ty :: ctx) (.G ty) → Term ctx (.G ty)

-- Most of the MeasurableSpace instance provided in
-- Mathlib.MeasureTheory.MeasurableSpace.Instances
@[reducible] noncomputable def Ty.denote : Ty → MeasCat
  | prod ty₁ ty₂ => .of (ty₁.denote × ty₂.denote)
  | bool => .of Bool
  | real => .of ℝ
  | exp n ty => .of (∀ (_ : Fin n), ty.denote) -- using MeasurableSpace.pi
  | index => .of ℕ
  | G ty => MeasCat.Giry.obj (ty.denote) --: Ty → Ty

end Appl
