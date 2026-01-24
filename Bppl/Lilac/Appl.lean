import Mathlib
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
  den : Ty → Type

notation "⟦" t "⟧" => Denotational.den t

class DenotationalMeas (Ty : Type u) extends Denotational Ty where
  instMeasurable : ∀ t, MeasurableSpace (den t)


instance instMeasurableSpaceDenotation {Ty : Type u} [d : DenotationalMeas Ty] (t : Ty) :
    MeasurableSpace ⟦t⟧ :=
  d.instMeasurable t

abbrev MeasurableFunction (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  := {f: α → β // Measurable f}

notation α " -m→ " β => {f: α → β // Measurable f}

-- TODO: The below two don't actually work, because of clash with indexing notation.
open MeasureTheory in
/-- Optionally provide non-standard domain φ-algebra -/
notation α " -m[ " φ₁  "]→ " β => {f: α → β // Measurable[φ₁] f}
open MeasureTheory in
/-- Optionally provide non-standard (co)domain φ-algebra -/
notation α " -m[ " φ₁ ", " φ₂ "]→ " β => {f: α → β // Measurable[φ₁, φ₂] f}

open NNReal MeasureTheory PMF Measurable ProbabilityTheory
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

inductive Arith where
  | add : Arith
  | sub : Arith
  | mul : Arith
  | div : Arith
  | pow : Arith

inductive Cmp where
  | lt : Cmp
  | le : Cmp
  | eq : Cmp

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
  | flip : (p : ℝ≥0) → (h : p ≤ 1) → Term ctx (.G .bool)
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
@[reducible] def Ty.den : Ty → MeasCat
  | prod ty₁ ty₂ => .of (ty₁.den × ty₂.den)
  | bool => .of Bool
  | real => .of ℝ
  | exp n ty => .of (∀ (_ : Fin n), ty.den) -- using MeasurableSpace.pi
  | index => .of ℕ
  | G ty => MeasCat.Measure.obj (ty.den) --: Ty → Ty

-- Is this already defined somewhere
-- also is there a more concise way to define measurable functions?
@[reducible] def Arith.den : Arith → (ℝ × ℝ) -m→ ℝ
  | add => ⟨fun (x,y) ↦ x + y, measurable_add⟩
  | sub => ⟨fun (x,y) ↦ x - y, measurable_sub⟩
  | mul => ⟨fun (x,y) ↦ x * y, measurable_mul⟩
  | div => ⟨fun (x,y) ↦ x / y, measurable_div⟩
  | pow => ⟨fun (x,y) ↦ x ^ y, measurable_pow⟩

def foo (p: ℝ × ℝ) : Bool := p.1 < p.2

lemma foop : Measurable (foo) := by
  rw [Measurable]
  intro t ht
  have h : t = ∅ ∨ t = {true} ∨ t = {false} ∨ t = Set.univ := by
    rcases em (true ∈ t) with ht' | ht' <;> rcases em (false ∈ t) with hf' | hf'
    · right; right; right; ext b; cases b <;> simp [*]
    · right; left; ext b; cases b <;> simp [*]
    · right; right; left; ext b; cases b <;> simp [*]
    · left; ext b; cases b <;> simp [*]
  rcases h with rfl | rfl | rfl | rfl
  · exact MeasurableSet.empty
  · have : foo ⁻¹' {true} = {p : ℝ × ℝ | p.1 < p.2} := by ext p; simp [foo]
    rw [this]
    exact isOpen_lt continuous_fst continuous_snd |>.measurableSet
  · have : foo ⁻¹' {false} = {p : ℝ × ℝ | p.1 < p.2}ᶜ := by ext p; simp [foo, not_lt]
    rw [this]
    exact (isOpen_lt continuous_fst continuous_snd).measurableSet.compl
  · exact MeasurableSet.univ

-- surely it shouldn't be this hard to show that the comparison operators are measurable
-- Either generalise over all of them or make a tactic
@[reducible] def Cmp.den : Cmp → (ℝ × ℝ) -m→ Bool
  | lt => ⟨fun p ↦ p.1 < p.2, foop⟩
  | le => ⟨fun p ↦ p.1 ≤ p.2, sorry⟩
  | eq => ⟨fun p ↦ p.1 = p.2, sorry⟩

instance : DenotationalMeas Ty where
  den ty := ↑ty.den
  instMeasurable ty := ty.den.2

-- Sadly Classes can't be annotate without reducible to. So the notation `⟦⟧` can't
-- may used through a type class and still be made reducible? Investigate
-- and at the same time I struggle to get type class inference to notice the M
@[simp] def Term.den : Term ctx ty → List.TProd (⟦·⟧) ctx -m→ ty.den
  | var mem => ⟨fun env ↦ env.get mem, List.TProd.measurable_get mem⟩
  | ret X => ⟨fun env ↦ .dirac (X.den.1 env),
      MeasureTheory.Measure.measurable_dirac.comp X.den.2⟩
  | bind M N => sorry -- the arguemnt `X` is the extra term in `N`'s context
  | pair M N => ⟨fun env ↦ (M.den.1 env, N.den.1 env), Measurable.prod M.den.2 N.den.2⟩
  | fst M => ⟨fun env ↦ (M.den.1 env).fst, Measurable.fst M.den.2⟩
  | snd M => ⟨fun env ↦ (M.den.1 env).snd, Measurable.snd M.den.2⟩
  | T => ⟨fun env ↦ true, measurable_const⟩
  | F => ⟨fun env ↦ false, measurable_const⟩
  | ite P M N => ⟨fun env ↦ if P.den.1 env then M.den.1 env else N.den.1 env,
      -- This is just a slightly finicky sorry, to show the function translating from bool to Prop
      -- is Measurable. Just need that as an additional lemma
      Measurable.ite (sorry) M.den.2 N.den.2⟩
  | flip p hp => ⟨fun _ ↦ (bernoulli p hp).toMeasure, measurable_const⟩
  | r x => ⟨fun _ ↦ x, measurable_const⟩
  | arith op M N => ⟨fun env ↦ op.den.1 (M.den.1 env, N.den.1 env),
    (op.den.2).comp (M.den.2.prod N.den.2)⟩
  | cmp op M N => ⟨fun env ↦ op.den.1 (M.den.1 env, N.den.1 env),
    (op.den.2).comp (M.den.2.prod N.den.2)⟩
  | unif01 => ⟨fun _ ↦ uniformOn (Set.Icc (0: ℝ) 1), measurable_const⟩
  | vect f => sorry --: (Fin n → Term ctx ty) → Term ctx (.exp n ty)
  | index N M => sorry -- : Term ctx .index → Term ctx (.exp n ty) → Term ctx ty
  -- No need to specify name for `i`: index and `X`: A, since we're using De brujin indices
  | «for» n Mᵢ Mₛ => sorry -- : ℕ → Term ctx ty → Term (index :: ty :: ctx) (.G ty) → Term ctx (.G ty)

end
end Appl
