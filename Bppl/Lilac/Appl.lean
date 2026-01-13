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

/-- Since we don't want to use our custom HList wiht the requirement of MeasurableSpace on our types
TProd provides a MeasurableSpace instance -/
def List.TProd.get : List.TProd β is → Member i is → β i
  | v, .head => v.1
  | v, .tail h => List.TProd.get v.2 h

theorem List.TProd.measurable_get [∀ i, MeasurableSpace (β i)] (mem : Member i is) :
    Measurable fun v : List.TProd β is => v.get mem := by
  induction mem with
  | head => exact measurable_fst
  | tail _ ih => exact ih.comp measurable_snd

class Denotational (Ty : Type u) where
  denote : Ty → Type

notation "⟦" t "⟧" => Denotational.denote t

class DenotationalMeas (Ty : Type u) extends Denotational Ty where
  instMeasurable : ∀ t, MeasurableSpace (denote t)


instance instMeasurableSpaceDenotation {Ty : Type u} [d : DenotationalMeas Ty] (t : Ty) :
    MeasurableSpace ⟦t⟧ :=
  d.instMeasurable t

abbrev MeasurableFunction (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  := {f: α → β // Measurable f}

notation α " -m→ " β => {f: α → β // Measurable f}

-- TODO: The below two don't actually work, because of clash with indexing notation.
open MeasureTheory in
/-- Optionally provide non-standard domain σ-algebra -/
notation α " -m[ " σ₁  "]→ " β => {f: α → β // Measurable[σ₁] f}
open MeasureTheory in
/-- Optionally provide non-standard (co)domain σ-algebra -/
notation α " -m[ " σ₁ ", " σ₂ "]→ " β => {f: α → β // Measurable[σ₁, σ₂] f}

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

noncomputable section
-- Most of the MeasurableSpace instance provided in
-- Mathlib.MeasureTheory.MeasurableSpace.Instances
@[reducible] def Ty.denote : Ty → MeasCat
  | prod ty₁ ty₂ => .of (ty₁.denote × ty₂.denote)
  | bool => .of Bool
  | real => .of ℝ
  | exp n ty => .of (∀ (_ : Fin n), ty.denote) -- using MeasurableSpace.pi
  | index => .of ℕ
  | G ty => MeasCat.Measure.obj (ty.denote) --: Ty → Ty

instance : DenotationalMeas Ty where
  denote ty := ↑ty.denote
  instMeasurable ty := ty.denote.2

-- Sadly Classes can't be annotate without reducible to. So the notation `⟦⟧` can't
-- may used through a type class and still be made reducible? Investigate
@[simp] def Term.denote : Term ctx ty → List.TProd (⟦·⟧) ctx -m→ ty.denote
  | var mem => ⟨fun env ↦ env.get mem, List.TProd.measurable_get mem⟩
  | ret X => ⟨fun env ↦ .dirac (X.denote.1 env),
      MeasureTheory.Measure.measurable_dirac.comp X.denote.2⟩
  | bind M N => sorry -- the arguemnt `X` is the extra term in `N`'s context
  | pair M N => sorry
  | fst M => sorry
  | snd M => sorry
  | T => sorry
  | F => sorry
  | ite M N O => sorry
  | flip p => sorry
  | r x => sorry
  | arith op M N => sorry
  | cmp op M N => sorry
  | unif01 => sorry --: Term ctx (.G .real)
  | vect f => sorry --: (Fin n → Term ctx ty) → Term ctx (.exp n ty)
  | index N M => sorry -- : Term ctx .index → Term ctx (.exp n ty) → Term ctx ty
  -- No need to specify name for `i`: index and `X`: A, since we're using De brujin indices
  | «for» n Mᵢ Mₛ => sorry -- : ℕ → Term ctx ty → Term (index :: ty :: ctx) (.G ty) → Term ctx (.G ty)

end
end Appl
