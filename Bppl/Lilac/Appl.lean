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

--TODO: 1) Make sure that some type has denotation `ℝ`
-- 2) The denotations must be measurable spaces which support equality
-- 3) Make a tactic to show that products of measurable spaces which support
-- equality also support equality
class DenotationalMeas (Ty : Type u) extends Denotational Ty where
  instMeasurable : ∀ t, MeasurableSpace (den t)


instance instMeasurableSpaceDenotation {Ty : Type u} [d : DenotationalMeas Ty] (t : Ty) :
    MeasurableSpace ⟦t⟧ :=
  d.instMeasurable t

abbrev MeasurableFun (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  := {f: α → β // Measurable f}

notation α " -m→ " β => MeasurableFun α β

instance instCoeMeasurableFun [MeasurableSpace α] [MeasurableSpace β] :
    CoeFun (α -m→ β) (fun _ => α → β) where
  coe f := f.val


-- TODO: The below two don't actually work, because of clash with indexing notation.
open MeasureTheory in
/-- Optionally provide non-standard domain σ-algebra -/
notation α " -m[ " σ₁  "]→ " β => {f: α → β // Measurable[σ₁] f}
open MeasureTheory in
/-- Optionally provide non-standard (co)domain σ-algebra -/
notation α " -m[ " σ₁ ", " σ₂ "]→ " β => {f: α → β // Measurable[σ₁, σ₂] f}

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

-- scoped notation ty₁ " × " ty₂ => Ty.prod ty₁ ty₂

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
  | pair : Term ctx ty₁ → Term ctx ty₂ → Term ctx (.prod ty₁ ty₂)
  | fst : Term ctx (.prod ty₁ ty₂) → Term ctx ty₁
  | snd : Term ctx (.prod ty₁ ty₂) → Term ctx ty₂
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
  | for : ℕ → Term ctx ty → Term (.index :: ty :: ctx) (.G ty) → Term ctx (.G ty)

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

def foo (p : ℝ × ℝ) : Bool := p.1 < p.2

lemma foop : Measurable (foo) := by
  -- apply measurable_to_bool -- much simpler method using this
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

instance arbitrary (ty : Ty) : Inhabited (ty.den.carrier) where
  default := match ty with
    | .prod ty₁ ty₂ =>
      (@default ty₁.den.carrier (arbitrary ty₁), @default ty₂.den.carrier (arbitrary ty₂))
    | (Ty.G ty) => Measure.dirac (@default ty.den.carrier (arbitrary ty))
    | Ty.index => default
    | Ty.exp _ ty => fun _ ↦ @default ty.den.carrier (arbitrary ty)
    | Ty.real => default
    | Ty.bool => default

-- Sadly Classes can't be annotate without reducible to. So the notation `⟦⟧` can't
-- may used through a type class and still be made reducible? Investigate
-- and at the same time I struggle to get type class inference to notice the M

/-- Takes the term and variable environment (which is a measurable function)
to give an element of a measurable space -/
@[simp] def Term.den : Term ctx ty → List.TProd (⟦·⟧) ctx -m→ ty.den
  | var mem => ⟨fun env ↦ env.get mem, List.TProd.measurable_get mem⟩
  | ret X => ⟨fun env ↦ .dirac (X.den.1 env),
      MeasureTheory.Measure.measurable_dirac.comp X.den.2⟩
  -- the arguemnt `X` is the extra term in `N`'s context
  -- sorry notes: `Measure.measurable_bind'` is not exactly what we want since
  -- `(fun X ↦ N.den.1 (X, env))` uses `env`
  | bind M N => ⟨fun env ↦ Measure.bind (M.den.1 env) (fun X ↦ N.den.1 (X, env)), sorry⟩
  | pair M N => ⟨fun env ↦ (M.den.1 env, N.den.1 env), Measurable.prod M.den.2 N.den.2⟩
  | fst M => ⟨fun env ↦ (M.den.1 env).fst, Measurable.fst M.den.2⟩
  | snd M => ⟨fun env ↦ (M.den.1 env).snd, Measurable.snd M.den.2⟩
  | T => ⟨fun env ↦ true, measurable_const⟩
  | F => ⟨fun env ↦ false, measurable_const⟩
  | ite P M N => ⟨fun env ↦ if P.den.1 env then M.den.1 env else N.den.1 env,
      -- This is just a slightly finicky sorry, to show the function translating from bool to Prop
      -- is Measurable. Just need that as an additional lemma
      Measurable.ite (by sorry) M.den.2 N.den.2⟩
  | flip p hp => ⟨fun _ ↦ (bernoulli p hp).toMeasure, measurable_const⟩
  | r x => ⟨fun _ ↦ x, measurable_const⟩
  | arith op M N => ⟨fun env ↦ op.den.1 (M.den.1 env, N.den.1 env),
    (op.den.2).comp (M.den.2.prod N.den.2)⟩
  | cmp op M N => ⟨fun env ↦ op.den.1 (M.den.1 env, N.den.1 env),
    (op.den.2).comp (M.den.2.prod N.den.2)⟩
  | unif01 => ⟨fun _ ↦ uniformOn (Set.Icc (0: ℝ) 1), measurable_const⟩
  -- not trivial sorry. Need to show the smalest σ-algebra generated out of the product,
  -- has inverse images measurable
  | vect f => ⟨fun env ↦ (fun n ↦ (f n).den.1 env), sorry⟩
  | @index _ len _ N M => ⟨fun env ↦
    let n : ℕ := (N.den.1 env)
    if h: n < len then (M.den.1 env) ⟨n, h⟩ else default, sorry⟩
  -- No need to specify name for `i`: index and `X`: A, since we're using De brujin indices
  | @«for» _ ty n Mᵢ Mₛ =>
    let rec loop (k : ℕ) (v : ⟦ty⟧) (f : ℕ → ⟦ty⟧ → Measure ⟦ty⟧) := if n ≤ k then
      .dirac v else
      Measure.bind (f k v) (fun v' ↦ loop (k+1) v' f)
    ⟨fun env ↦ loop 1 (Mᵢ.den env) fun k v ↦ Mₛ.den (k, (v, env)), sorry⟩

end
end Appl
