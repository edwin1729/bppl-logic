import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl

set_option autoImplicit true
set_option relaxedAutoImplicit true


/- Here are we are parametric over the denotation of types in APPL.
To remain general, we assume there are two kinds of types in APPL,
whose dentotation is 1) `Meas` 2) `Set`

(Though in our actual definition of APPL, all types have denotation in `Meas` and every element
of `Meas` is also in `Set`)-/

/- Questions

-- Do we really need a measurable space on the domain of D and D to be measurable?
-- and why do we need finite footprint?o

-- Interesting that measure on the hilbert cube is not uniform, or is it?
-- for σ-algebra with finite footprint at least??

-/

open MeasureTheory

/- `TyRand` and `TyDet` need to have a denotation function. Additionally `TyRand`'s
denotation must have a measurable space structure -/
variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]

/-- Deterministic Value -/
abbrev detVal (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → ⟦A⟧)

/-- Random Value -/
abbrev randVal (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ ⟦A⟧)

/-- Deterministic distribution -/
abbrev detDist (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → Measure ⟦A⟧)

/-- Random distribution -/
abbrev randDist (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ Measure ⟦A⟧)

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

/-- Todo add finite footprint condition -/
abbrev RV (A : Type) [MeasurableSpace A] := HC -m→ A

/-- Lilac propositions -/
abbrev lProp (ds : List TyDet) (rs : List TyRand) :=
  HList (⟦·⟧) ds → RV (List.TProd (⟦·⟧) rs) → PSp HC → Prop

-- Using `MeasurableSpace.pi`
instance : MeasurableSpace HC := inferInstance

namespace MeasurableFunc
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def comp (g : β -m→ γ) (f : α -m→ β)
  : α -m→ γ := ⟨g.1 ∘ f.1, Measurable.comp g.2 f.2⟩

notation g " ∘ " f => comp g f

def fun_prod (f : α -m→ β) (g : α -m→ γ) : α -m→ β × γ :=
  ⟨fun a ↦ (f a, g a), Measurable.prod f.2 g.2⟩

notation x " ; " xs => fun_prod x xs

end MeasurableFunc

namespace lProp

-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand}

-- The idea is to get a singleton set of a ∀ or ∀ᵣᵥ assertion as input and the same term
-- as output (when taking denotation). So the ds and rs type indices are the same
def sForall (Ψ : lProp ds rs → Prop)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ P, Ψ P → P γ D φ

def top : lProp ds rs := fun _ _ _ ↦ True
def bot : lProp ds rs := fun _ _ _ ↦ False

def and (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  P γ D φ ∧ Q γ D φ
def or (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  P γ D φ ∨ Q γ D φ
def imp (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φ', φ ≤ φ' → P γ D φ' → Q γ D φ'
def sep (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ φ₁ φ₂ : PSp HC, φ₁ ⋆ φ₂ ≤ some φ ∧ P γ D φ₁ ∧ Q γ D φ₂
def wand (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φp, ∃ φq, φp ⋆ φ = some φq ∧ (P γ D φp → Q γ D φq)

def persistently (P : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  P γ D 1

-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ x : ⟦d⟧, P (x :: γ) D φ
def «exists» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ x : ⟦d⟧, P (x :: γ) D φ
def forall_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ X : RV ⟦r⟧, P γ (X ; D) φ
def exists_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ X : RV ⟦r⟧, P γ (X ; D) φ

def own (E : randVal ds rs A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  Measurable[φ.1] ((E γ).1 ∘ D.1)

def dist (E : randVal ds rs A) (μ : detDist ds A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  Measurable[φ.1] ((E γ).1 ∘ D.1) ∧ μ γ = .bind φ.2 (fun ω ↦ Measure.dirac (E γ (D ω)))

-- confirm if (X₁, X₂)⁻¹ (A) = X₁⁻¹ (A) ∪ X₂⁻¹ (A) ∪
-- Do we need different types A₁ and A₂ (what's the use of almost sure equality)
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ
def eq (E₁ E₂ : randVal ds rs A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  let X₁ := (E₁ γ).1 ∘ D.1
  let X₂ := (E₂ γ).1 ∘ D.1
  -- let F := {ω | X₁ ω = X₂ ω}
  sorry --: randVal ds rs A → randVal ds rs A → Term ds rs -- almost sure equality

-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : randDist ds rs A) (Q : lProp ds (A :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φ_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
  φ_fr ⋆ φ ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
  ∃ X : RV ⟦A⟧, ∃ φ' : PSp HC,
  ∃ μ' : ProbabilityMeasure HC, φ_fr ⋆ φ' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q γ (X ; D) φ'

end lProp

/-- Satisfaction relation: `(γ, D, φ)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `φ` -/
notation:50 "(" γ ", " D ", " φ ")⊨ " P => Assertion.denote P γ D φ

open Iris.BI Iris

-- abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop

-- Instantiate basic connectives in BI

instance instBIBase {ds : List TyDet} {rs : List TyRand} : BIBase (lProp ds rs) where
  Entails P Q    := ∀ γ D φ, P γ D φ → Q γ D φ
  emp            := sorry --φ = 1
  pure φ         := sorry --φ
  and            := .and
  or             := .or
  imp            := .imp
  sForall        := .sForall
  -- iExists      := .iExists
  sep        := .sep
  wand       := .wand
  -- could we do ttesorry --r than this? Identify what more is persistent/affine
  -- wasn't BaSL rtisorry --ally affine? What does that mean?
  persistently := .persistently
  later P        := sorry --P φ -- there is no step indexing

-- instance {α : Type*} [nonempty : Nonempty α] : COFE (PROP α) := COFE.ofDiscrete Eq equivalence_eq

-- instance instBI {α : Type*} [nonempty : Nonempty α] : BI (PROP α) where
--   equiv_iff := sorry
--   entails_preorder := sorry
--   and_ne := sorry
--   or_ne := sorry
--   imp_ne := sorry
--   sForall_ne := sorry
--   sExists_ne := sorry
--   sep_ne := sorry
--   wand_ne := sorry
--   persistently_ne := sorry
--   later_ne := sorry
--   pure_intro := sorry
--   pure_elim' := sorry
--   and_elim_l := sorry
--   and_elim_r := sorry
--   and_intro := sorry
--   or_intro_l := sorry
--   or_intro_r := sorry
--   or_elim := sorry
--   imp_intro := sorry
--   imp_elim := sorry
--   sForall_intro := sorry
--   sForall_elim := sorry
--   sExists_intro := sorry
--   sExists_elim := sorry
--   sep_mono := sorry
--   emp_sep := sorry
--   sep_symm := sorry
--   sep_assoc_l := sorry
--   wand_intro := sorry
--   wand_elim := sorry
--   persistently_mono := sorry
--   persistently_idem_2 := sorry
--   persistently_emp_2 := sorry
--   persistently_and_2 := sorry
--   persistently_sExists_1 := sorry
--   persistently_absorb_l := sorry
--   persistently_and_l := sorry
--   later_mono := sorry
--   later_intro := sorry
--   later_sForall_2 := sorry
--   later_sExists_false := sorry
--   later_sep := sorry
--   later_persistently := sorry
--   later_false_em := sorry
