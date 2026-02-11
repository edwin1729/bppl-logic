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

/-- Lilac propositions -/
abbrev lProp (ds : List TyDet) (rs : List TyRand) :=
  EnvDet ds → EnvRand rs → PSp HC → Prop

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
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ P, Ψ P → P γ D Ω

def sExists (Ψ : lProp ds rs → Prop)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ P, Ψ P → P γ D Ω

def pure (φ : Prop) : lProp ds rs := fun _ _ _ ↦ φ
def emp : lProp ds rs := fun _ _ Ω ↦ Ω = 1

def top : lProp ds rs := fun _ _ _ ↦ True
def bot : lProp ds rs := fun _ _ _ ↦ False

def and (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  P γ D Ω ∧ Q γ D Ω
def or (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  P γ D Ω ∨ Q γ D Ω
def imp (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ω', Ω ≤ Ω' → P γ D Ω' → Q γ D Ω'
def sep (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ Ω₁ Ω₂ : PSp HC, Ω₁ ⋆ Ω₂ ≤ some Ω ∧ P γ D Ω₁ ∧ Q γ D Ω₂
def wand (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ωp, ∃ Ωq, Ωp ⋆ Ω = some Ωq ∧ (P γ D Ωp → Q γ D Ωq)

def persistently (P : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (_ : PSp HC) : Prop :=
  P γ D 1

-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ x : ⟦d⟧, P (x :: γ) D Ω
def «exists» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ x : ⟦d⟧, P (x :: γ) D Ω
def forall_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ X : RV ⟦r⟧, P γ (X ; D) Ω
def exists_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ X : RV ⟦r⟧, P γ (X ; D) Ω

def own (E : ValRand ds rs A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  Measurable[Ω.1] ((E γ).1 ∘ D.1)

def dist (E : ValRand ds rs A) (μ : DistDet ds A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  Measurable[Ω.1] ((E γ).1 ∘ D.1) ∧ μ γ = .bind Ω.2 (fun ω ↦ Measure.dirac (E γ (D ω)))

-- confirm if (X₁, X₂)⁻¹ (A) = X₁⁻¹ (A) ∪ X₂⁻¹ (A) ∪
-- Do we need different types A₁ and A₂ (what's the use of almost sure equality)
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ
def eq (E₁ E₂ : ValRand ds rs A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  let X₁ := (E₁ γ).1 ∘ D.1
  let X₂ := (E₂ γ).1 ∘ D.1
  -- let F := {ω | X₁ ω = X₂ ω}
  sorry --: randVal ds rs A → randVal ds rs A → Term ds rs -- almost sure equality

-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : DistRand ds rs A) (Q : lProp ds (A :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ω_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
  Ω_fr ⋆ Ω ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
  ∃ X : RV ⟦A⟧, ∃ Ω' : PSp HC,
  ∃ μ' : ProbabilityMeasure HC, Ω_fr ⋆ Ω' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q γ (X ; D) Ω'

end lProp

/- Satisfaction relation: `(γ, D, Ω)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `Ω` -/
-- notation:50 "(" γ ", " D ", " Ω ")⊨ " P => Assertion.denote P γ D Ω

namespace BI
open Iris.BI Iris
-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand}

-- abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop

-- Instantiate basic connectives in BI

instance instBIBase : BIBase (lProp ds rs) where
  Entails P Q    := ∀ γ D Ω, P γ D Ω → Q γ D Ω
  emp            := .emp
  pure           := .pure
  and            := .and
  or             := .or
  imp            := .imp
  sForall        := .sForall
  sExists        := .sExists
  sep            := .sep
  wand           := .wand
  -- could we do better than this? Identify what more is persistent/affine
  -- wasn't BaSL partially affine? What does that mean?
  persistently   := .persistently
  later P        := P -- there is no step indexing

instance : Std.Preorder (Entails (PROP := lProp ds rs)) where
  refl := by
    simp only [BI.Entails]
    intro _ _ _ _ h
    exact h
  trans := by
    simp only [BI.Entails]
    intro _ _ _ h_xy h_yz γ D Ω h_x
    apply h_yz γ D Ω
    apply h_xy γ D Ω
    exact h_x

instance {ds : List TyDet} {rs : List TyRand} : COFE (lProp ds rs) :=
  COFE.ofDiscrete Eq equivalence_eq

instance instBI {ds : List TyDet} {rs : List TyRand} : BI (lProp ds rs) where
  entails_preorder := by infer_instance
  equiv_iff {P Q} := ⟨
    fun h : P = Q => h ▸ ⟨refl, refl⟩,
    fun ⟨h₁, h₂⟩ => by ext γ D Ω; exact ⟨h₁ γ D Ω, h₂ γ D Ω⟩
  ⟩
  and_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  or_ne           := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  imp_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  sep_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  wand_ne         := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  persistently_ne := ⟨by rintro _ _ _ rfl; rfl⟩
  later_ne        := ⟨by rintro _ _ _ rfl; rfl⟩
  sForall_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl
  sExists_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl


end BI
