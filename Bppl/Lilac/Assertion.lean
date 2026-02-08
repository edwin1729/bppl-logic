import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl
/-!
Will need the subtly different types of objects (in the semantic domain) that variables that
variables can be interpreted to, to be defined, as certain types are allowed to be used in
connectives of Lilac.

Each of these variables (terms) will need to be interpreted under an environment.

Use `env` for the values and `ctx` for the types of these values.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true


-- Define the various kinds of measurable fucntions we'll have to deal with
-- Fig 4. in Lilac paper, but why do we need that? For example `own E` is an assertion
-- which requires the definition of `E` as in `T-RANDE`

/- Here are we are parametric over the denotation of types in APPL.
To remain general, we assume there are two kinds of types in APPL,
whose dentotation is 1) `Meas` 2) `Set`

(Though in our actual definition of APPL, all types have denotation in `Meas` and every element
of `Meas` is also in `Set`)-/

-- TODO introduce notation for Measurable fns
-- TODO we might want to have an MList of types which are measurable, and specialize the development
-- here to use just that. Depends on how we would instantiate the types here come APPL.
-- For now I keep it verbose with casts like `(fun i => ↑(β i)) is`, keeping in mind the
-- direction of succinctness


-- instance instMeasurableProd : MeasurableSpace (MList β is) where
-- universe u₁ u₂
-- abbrev RV {β₁ : α₁ → Type u₁} {is : List α₁} -- The deterministic env
--     {β₂ : α₂ → Type u₂} {is' : List α₂} -- The probabilistic env which needs to be measurable
--     (A : Type) [MeasurableSpace A] :=
--   {f : ∀ a, }
  --HList β₁ is → A--{ f : HList β₂ is' → A // Measurable f }

-- attempt to at defining an Assertion. Plan: copy dependent de Brujin indicies
-- with "Term" being assertion and denotation being semantics as expected.


-- we're struggling to see how to couple the logic with the language. So let's tackle that
-- separately, and for the moment let

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


-- inductive Foo where
--   | fill : (Foo → Prop) → Foo
inductive Assertionn : List TyDet → List TyRand → Type
  | iForall : ∀ {α}, (α → Assertionn ds rs) → Assertionn ds rs

inductive Assertionnn : List TyDet → List TyRand → Type
  | sForall : (Assertionnn ds rs → Prop) → Assertionnn ds rs

-- Here Term means Assertion actually
inductive Assertion : List TyDet → List TyRand → Type
  -- | var   : Member ty ctx → Term ctx
  | top : Assertion ds rs -- ds: deterministic context, rs: random variable context
  | bot : Assertion ds rs
  | and  : Assertion ds rs  → Assertion ds rs → Assertion ds rs
  | or  : Assertion ds rs  → Assertion ds rs → Assertion ds rs
  | imp  : Assertion ds rs  → Assertion ds rs → Assertion ds rs
  | sep  : Assertion ds rs  → Assertion ds rs → Assertion ds rs
  | wand : Assertion ds rs  → Assertion ds rs → Assertion ds rs
  | persistently  : Assertion ds rs  → Assertion ds rs
  | forall (d : TyDet) : Assertion (d :: ds) rs → Assertion ds rs
  | exists (d : TyDet) : Assertion (d :: ds) rs → Assertion ds rs
  -- is it a problem that only types at the head of the list can be quantified over?
  | forall_rv (r : TyRand) : Assertion ds (r :: rs) → Assertion ds rs
  | exists_rv (r : TyRand) : Assertion ds (r :: rs) → Assertion ds rs
  -- The idea is to get a singleton set of a ∀ or ∀ᵣᵥ assertion as input and the same term
  -- as output (when taking denotation). So the ds and rs type indices are the same
  -- | sForall : (Ψ : Assertion ds rs → Prop) → Assertion ds rs
  | iForall : ∀ {α}, (α → Assertion ds rs) → Assertion ds rs
  -- | sExists : (Ψ : Assertion ds rs → Prop) → Assertion ds rs
  -- | iExists : ∀ α, (α → Assertion ds rs) → Assertion ds rs
  -- | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  -- | let : Term ctx ty₁ → Term (ty₁ :: ctx) ty₂ → Term ctx ty₂
  | own : randVal ds rs A → Assertion ds rs
  | dist : randVal ds rs A → detDist ds A → Assertion ds rs
  | eq : randVal ds rs A₁ → randVal ds rs A₂ → Assertion ds rs -- almost sure equality
  -- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
  -- denotation is ℝ
  | wp : randDist ds rs A → Assertion ds (A :: rs) → Assertion ds rs


-- ⊤ | ⊥ | 𝑃 ∧ 𝑄 | 𝑃 ∨ 𝑄 | 𝑃 → 𝑄 |
-- 𝑃 ∗ 𝑄 | 𝑃 −∗ 𝑄 | □ 𝑃 |
-- ∀𝑥:𝑆.𝑃 | ∃𝑥:𝑆.𝑃 | ∀rv𝑋 :𝐴.𝑃 | ∃rv𝑋 :𝐴.𝑃 |
-- 𝐸 ∼ 𝜇 | own 𝐸 | 𝐸 =as= 𝐸 | E[𝐸] = 𝑒 | wp(𝑀, 𝑋 :𝐴.𝑄)

-- now define semantics for these "Terms". Then use said semantics
-- in definition of `Entails`.

-- Haziest in my mind: 1) wp semantics 2) instantiations of `TyDet` and `TyRand`

-- does the order of parameters matter? For purposes of dependencies?
-- If not I would like it to be in the order γ → D → 𝒫 → P → Prop
-- for encoding the four way satisfiabilty relation: γ, D 𝒫 ⊨ P
variable {α : Type*} [nonempty : Nonempty α]

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

-- Using `MeasurableSpace.pi`
instance : MeasurableSpace HC := inferInstance

-- def RV (A : Type) [MeausurableSpace A] := {f : α → A // measurable }

-- This section was made originally to be used with `own E` or any other probability specfic
-- connectives. But we may not need this at all, since `Own E` is alway `True` if one is able
-- to construct an `E` in the first place!
namespace MeasurableFunc
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def comp (g : β -m→ γ) (f : α -m→ β)
  : α -m→ γ := ⟨g.1 ∘ f.1, Measurable.comp g.2 f.2⟩

notation g " ∘ " f => comp g f

def fun_prod (f : α -m→ β) (g : α -m→ γ) : α -m→ β × γ :=
  ⟨fun a ↦ (f a, g a), Measurable.prod f.2 g.2⟩

notation x " ; " xs => fun_prod x xs

end MeasurableFunc

/-- Todo add finite footprint condition -/
abbrev RV (A : Type) [MeasurableSpace A] := HC -m→ A

-- abbrev RV' (rs : List TyRand) := HC -m→ (List.TProd (⟦·⟧) rs)

-- Do we really need a measurable space on the domain of D and D to be measurable?
-- and why do we need finite footprint?o

-- Interesting that measure on the hilbert cube is not uniform, or is it?
-- for σ-algebra with finite footprint at least??

-- γ, φ ⊨ P

@[simp] noncomputable def Assertion.denote {ds : List TyDet} {rs : List TyRand}
    (P : Assertion ds rs) (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  match P with
  | top  => True
  | bot  => False
  | and P Q => P.denote γ D φ ∧ Q.denote γ D φ
  | or P Q => P.denote γ D φ ∨ Q.denote γ D φ
  | imp P Q => ∀ φ', φ ≤ φ' → P.denote γ D φ' → Q.denote γ D φ'
  | sep P Q => ∃ φ₁ φ₂ : PSp HC, φ₁ ⋆ φ₂ ≤ some φ ∧ P.denote γ D φ₁ ∧ Q.denote γ D φ₂
  | wand P Q => ∀ φp, ∃ φq, φp ⋆ φ = some φq ∧ (P.denote γ D φp → Q.denote γ D φq)
  | persistently P => P.denote γ D 1
  | «forall» d P => ∀ x : ⟦d⟧, P.denote (x :: γ) D φ
  | «exists» d P => ∃ x : ⟦d⟧, P.denote (x :: γ) D φ
  | forall_rv r P => ∀ X : RV ⟦r⟧, P.denote γ (X ; D) φ
  | exists_rv r P => ∃ X : RV ⟦r⟧, P.denote γ (X ; D) φ
  | own E => Measurable[φ.1] ((E γ).1 ∘ D.1)
  |
  | dist E μ => Measurable[φ.1] ((E γ).1 ∘ D.1) ∧
      μ γ = .bind φ.2 (fun ω ↦ Measure.dirac (E γ (D ω)))
  -- confirm if (X₁, X₂)⁻¹ (A) = X₁⁻¹ (A) ∪ X₂⁻¹ (A) ∪
  -- Do we need different types A₁ and A₂ (what's the use of almost sure equality)
  | eq E₁ E₂ =>
    let X₁ := (E₁ γ).1 ∘ D.1
    let X₂ := (E₂ γ).1 ∘ D.1
    -- let F := {ω | X₁ ω = X₂ ω}
    sorry --: randVal ds rs A → randVal ds rs A → Term ds rs -- almost sure equality
    -- consider just taking another PSp instead of μ, if it might simplify proof later
  | @wp _ _ _ _ _ _ A M Q => ∀ φ_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
      φ_fr ⋆ φ ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
      ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
      ∃ X : RV ⟦A⟧, ∃ φ' : PSp HC,
      ∃ μ' : ProbabilityMeasure HC, φ_fr ⋆ φ' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
      (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
        (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
      Q.denote γ (X ; D) φ'

/-- Satisfaction relation: `(γ, D, φ)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `φ` -/
notation:50 "(" γ ", " D ", " φ ")⊨ " P => Assertion.denote P γ D φ

-- open Iris.BI Iris

class BIBase (PROP : Type u) where
  Entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  iForall : ∀ {α}, (α → PROP) → PROP
  -- iExists : ∀ {α}, (α → PROP) → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  persistently : PROP → PROP
  later : PROP → PROP

-- abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop
-- def PROP := ∀ ds : List TyDet, ∀ rs : List TyRand, @Term TyDet TyRand td tdm ds rs
-- Instantiate basic connectives in BI

instance instBIBase {ds : List TyDet} {rs : List TyRand} : BIBase (Assertion ds rs) where
  Entails P Q    := ∀ γ D φ, P.denote γ D φ → Q.denote γ D φ
  emp            := sorry --φ = 1
  pure φ         := sorry --φ
  and            := .and
  or             := .or
  imp            := .imp
  iForall        := .iForall
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
