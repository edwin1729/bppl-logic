import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

-- import Bppl.Lilac.KRM
import Bppl.Lilac.Appl
import Bppl.Lilac.BI

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
abbrev ValDet (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → ⟦A⟧)

/-- Random Value -/
abbrev ValRand (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ ⟦A⟧)

/-- Deterministic distribution -/
abbrev DistDet (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → Measure ⟦A⟧)

/-- Random distribution -/
abbrev DistRand (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ Measure ⟦A⟧)

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

/-- Todo add finite footprint condition -/
abbrev RV (A : Type) [MeasurableSpace A] := HC -m→ A

abbrev EnvDet (ds : List TyDet) := HList (⟦·⟧) ds
abbrev EnvRand (rs : List TyRand) := RV (List.TProd (⟦·⟧) rs)

-- abbrev LProp (ds : List TyDet) (rs : List TyRand) :=
--   EnvDet ds → EnvRand rs → PSp HC → Prop

open Iris.Instances.Intuitionistic
open Iris.Instances.Intuitionistic.instBIBase

/-- Lilac propositions -/
abbrev LProp (ds : List TyDet) (rs : List TyRand) :=
  IProp (EnvDet ds × EnvRand rs) (PSp HC)

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

namespace LProp

-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand}

-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : LProp (d :: ds) rs) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∀ x : ⟦d⟧, P.1 ((x :: γ), D) Ω, sorry⟩
def «exists» (d : TyDet) (P : LProp (d :: ds) rs) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∃ x : ⟦d⟧, P.1 ((x :: γ), D) Ω, sorry⟩
def forall_rv (r : TyRand) (P : LProp ds (r :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∀ X : RV ⟦r⟧, P.1 (γ, (X ; D)) Ω, sorry⟩
def exists_rv (r : TyRand) (P : LProp ds (r :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∃ X : RV ⟦r⟧, P.1 (γ, (X ; D)) Ω, sorry⟩

def own (E : ValRand ds rs A) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ Measurable[Ω.1] ((E γ).1 ∘ D.1), sorry⟩

def dist (E : ValRand ds rs A) (μ : DistDet ds A) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦
    Measurable[Ω.1] ((E γ).1 ∘ D.1) ∧ μ γ = .bind Ω.2 (fun ω ↦ Measure.dirac (E γ (D ω)))
  , sorry⟩

-- TODO
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ

def eq (E₁ E₂ : ValRand ds rs A) : LProp ds rs :=
  ⟨fun (γ, D) ⟨ℱ, μ, hμ⟩ ↦
    let X₁ := (E₁ γ).1 ∘ D.1
    let X₂ := (E₂ γ).1 ∘ D.1
    let F := {ω | X₁ ω = X₂ ω}
    MeasurableSet[ℱ] F ∧ μ F = 1 ∧
    -- inverse of a function from a point to a set is being taken here
    ∀ x₁ x₂ : ⟦A⟧, MeasurableSet[ℱ] (F ∪ (X₁⁻¹' {x₁}) ∪ (X₂⁻¹' {x₂}))
    , sorry⟩

-- The extension `rs' ++ rs` may not be necessary
-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : DistRand ds rs A) (Q : LProp ds (A :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦
  ∀ Ω_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
  Ω_fr ⋆ Ω ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
  ∃ X : RV ⟦A⟧, ∃ Ω' : PSp HC,
  ∃ μ' : ProbabilityMeasure HC, Ω_fr ⋆ Ω' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q.1 (γ, (X ; D)) Ω'
  , sorry⟩

syntax:52 term:53 " ∼ " term:53 : term

macro_rules
  | `(iprop($rv ∼ $dist)) => `(dist $rv $dist)

delab_rule dist
  | `($_ $rv $dist) => `(iprop($rv ∼ $dist))

syntax:54 term:53 " ≗ " term:53 : term

macro_rules
  | `(iprop($E₁ ≗ $E₂)) => `(eq $E₁ $E₂)

delab_rule eq
  | `($_ $E₁ $E₂) => `(iprop($E₁ ≗ $E₂))

end LProp

/- Satisfaction relation: `(γ, D, Ω)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `Ω` -/
-- notation:50 "(" γ ", " D ", " Ω ")⊨ " P => Assertion.denote P γ D Ω
