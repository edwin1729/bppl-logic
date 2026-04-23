/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence
import Iris.ProofMode

-- import Bppl.Lilac.KRM
import Bppl.Lilac.Appl
import Bppl.Lilac.BI

set_option autoImplicit true
set_option relaxedAutoImplicit true


/-! Here are we are parametric over the denotation of types in APPL.
To remain general, we assume there are two kinds of types in APPL,
whose dentotation is 1) `Meas` 2) `Set`

(Though in our actual definition of APPL, all types have denotation in `Meas` and every element
of `Meas` is also in `Set`)

TODO:
Only `own` allows its `ValRand` "output" type to be an Arbitrary measurable space. This is done
because otherwise, in the `congruence` proof rule, we would require `DenotationalMeas` to specify
some way of taking the product type.

But now only `own` is given this special treatment. I find it hard to determine the effects of this
choice so I make minimal changes as per requirements in `congruence` rule.
-/

open MeasureTheory Appl.Denotation
open List (TProd)

abbrev fProd {α β γ : Type*} (f : α → β) (g : α → γ) (x : α) : β × γ := (f x, g x)
notation " ⟨ " f ", " g " ⟩ᶠ " => fProd f g
namespace MeasurableFunc
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def comp (g : β -m→ γ) (f : α -m→ β)
  : α -m→ γ := ⟨g.1 ∘ f.1, Measurable.comp g.2 f.2⟩

notation g " ∘ₘ " f => comp g f

def fun_prod (f : α -m→ β) (g : α -m→ γ) : α -m→ β × γ :=
  ⟨fun a ↦ (f a, g a), Measurable.prod f.2 g.2⟩

notation x " ; " xs => fun_prod x xs

/- Note that for the deterministic env, `cons` is just pair, `(· , ·)`,
by the definition of List.TProd. -/

end MeasurableFunc

/- `TyRand` and `TyDet` need to have a denotation function. Additionally `TyRand`'s
denotation must have a measurable space structure -/
variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]

/-- The same construction with TProd is used for both Determinisitic and Random Environments. -/
abbrev Env [Denotational Ty] (ds : List Ty) := TProd (⟪·⟫) ds

/-- Deterministic Value -/
abbrev ValDet (ds : List TyDet) (α : Type) [MeasurableSpace α] := (Env ds → α)

/-- Random Value -/
abbrev ValRand (ds : List TyDet) (rs : List TyRand) (α : Type*) [MeasurableSpace α] :=
  (Env ds → List.TProd (⟪·⟫) rs -m→ α)

/-- Deterministic distribution -/
abbrev DistDet (ds : List TyDet) (α : Type) [MeasurableSpace α] := (Env ds → Measure α)

/-- Random distribution -/
abbrev DistRand (ds : List TyDet) (rs : List TyRand) (α : Type) [MeasurableSpace α] :=
  (Env ds → List.TProd (⟪·⟫) rs -m→ Measure α)

/- Substitutions: -/

abbrev substValDet {ds ds' : List TyDet} {α : Type} [MeasurableSpace α] (s : Env ds' → Env ds)
    (e : ValDet ds α) : ValDet ds' α :=
  e ∘ s

/-- add the det env as input to `S`. Required by the `congruence` proof rule.
Unclear whether this cuases further complications... -/
abbrev substValRand {ds ds' : List TyDet} {rs rs' : List TyRand} {α : Type} [MeasurableSpace α]
    (s : Env ds' → Env ds) (S : Env ds' → Env rs' -m→ Env rs) (E : ValRand ds rs α)
    : ValRand ds' rs' α :=
  fun γ ↦ E (s γ) ∘ₘ (S γ)

abbrev substDistDet {ds ds' : List TyDet} {α : Type} [MeasurableSpace α] (s : Env ds' → Env ds)
    (μ : DistDet ds α) : DistDet ds' α :=
  μ ∘ s

abbrev substDistRand {ds ds' : List TyDet} {rs rs' : List TyRand} {α : Type} [MeasurableSpace α]
    (s : Env ds' → Env ds) (S : Env ds' → Env rs' -m→ Env rs) (M : DistRand ds rs α)
    : DistRand ds' rs' α :=
  fun γ ↦ M (s γ) ∘ₘ (S γ)

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

abbrev borel_ms_HC : MeasurableSpace HC := MeasurableSpace.pi

instance : Inhabited HC where
  default := fun _ ↦ 0

/-- Todo add finite footprint condition -/
abbrev RV (α : Type) [MeasurableSpace α] := @MeasurableFun HC α MeasurableSpace.pi _

abbrev EnvDet (ds : List TyDet) := TProd (⟪·⟫) ds
abbrev EnvRand (rs : List TyRand) := RV (TProd (⟪·⟫) rs)

open Iris.Instances.Intuitionistic
open Iris.Instances.Intuitionistic.instBIBase

/-- Lilac propositions -/
abbrev LProp (ds : List TyDet) (rs : List TyRand) :=
  IProp (EnvDet ds × EnvRand rs) (PSpace HC)

-- Using `MeasurableSpace.pi`
instance : MeasurableSpace HC := inferInstance

namespace LProp

-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand} {A : TyRand}
-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : LProp (d :: ds) rs) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∀ x : ⟪d⟫, P.1 ((x, γ), D) Ω, sorry⟩
def «exists» (d : TyDet) (P : LProp (d :: ds) rs) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∃ x : ⟪d⟫, P.1 ((x, γ), D) Ω, sorry⟩
def forall_rv (r : TyRand) (P : LProp ds (r :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∀ X : RV ⟪r⟫, P.1 (γ, (X ; D)) Ω, sorry⟩
def exists_rv (r : TyRand) (P : LProp ds (r :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ ∃ X : RV ⟪r⟫, P.1 (γ, (X ; D)) Ω, sorry⟩

def own [MeasurableSpace α] (E : ValRand ds rs α) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦ Measurable[Ω.ms] ((E γ).1 ∘ D.1), sorry⟩

def dist (E : ValRand ds rs ⟪A⟫) (μ : DistDet ds ⟪A⟫) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦
    Measurable[Ω.ms] ((E γ).1 ∘ D.1) ∧ μ γ = .bind Ω.μ (fun ω ↦ Measure.dirac (E γ (D ω)))
  , sorry⟩

-- TODO
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ

notation "⟪" ty "⟫'" => DenotationalMeas.instMeasurable ty

-- We do not use `ae` filter and general mathlib infrastructure, because these don't give the
-- very particular measurability of spaces that we require
def eq (E₁ E₂ : ValRand ds rs ⟪A⟫) : LProp ds rs :=
  ⟨fun (γ, D) ⟨⟨ℱ, μ⟩, hμ⟩ ↦
    let X₁ := (E₁ γ).1 ∘ D.1
    let X₂ := (E₂ γ).1 ∘ D.1
    let F := {ω | X₁ ω = X₂ ω}
    MeasurableSet[ℱ] F ∧ μ F = 1 ∧
    -- (F ∪ ⟨X₁, X₂⟩ᶠ⁻¹' ·) '' (⟪A⟫ᵐ.prod ⟪A⟫ᵐ).MeasurableSet' ⊆ ℱ.MeasurableSet'
    ∀ x :Set (⟪A⟫ × ⟪A⟫), MeasurableSet x →
      MeasurableSet[ℱ] (F ∪ (fun ω ↦ (X₁ ω, X₂ ω))⁻¹' x)
    , sorry⟩

def PSpace.mk' {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω) : PSpace Ω :=
  ⟨⟨_, μ.1⟩, μ.2⟩

-- The extension `rs' ++ rs` may not be necessary
-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : DistRand ds rs ⟪A⟫) (Q : LProp ds (A :: rs)) : LProp ds rs :=
  ⟨fun (γ, D) Ω ↦
  ∀ Ω_fr : PSpace HC, ∀ μ : ProbabilityMeasure HC,
  Ω_fr ⋆ Ω ≤ some (PSpace.mk' μ) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟪·⟫) (rs' ++ rs)),
  ∃ X : RV ⟪A⟫, ∃ Ω' : PSpace HC,
  ∃ μ' : ProbabilityMeasure HC, Ω_fr ⋆ Ω' ≤ some (PSpace.mk' μ) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q.1 (γ, (X ; D)) Ω'
  , sorry⟩

open Iris.BI

syntax:52 term:53 " ∼ " term:53 : term

macro_rules
  | `(iprop($rv ∼ $dist)) => `(dist $rv $dist)

delab_rule dist
  | `($_ $rv $dist) => do ``(iprop($(← unpackIprop rv) ∼ iprop($(← unpackIprop dist))))

syntax:54 term:53 " ≗ " term:53 : term

macro_rules
  | `(iprop($E₁ ≗ $E₂)) => `(eq $E₁ $E₂)

delab_rule eq
  | `($_ $E₁ $E₂) => do ``(iprop($(← unpackIprop E₁) ≗ $(← unpackIprop E₂)))

-- Why am I needing to use nested iprop when using this notation??
-- My delab rules are naive, they need to use unpack?
-- syntax:52 " ∀ᵣᵥ: " term:53 " , " term:53 : term

-- macro_rules
--   | `(iprop(∀ᵣᵥ: $A , $P)) => `(forall_rv $A $P)

-- delab_rule eq
--   | `($_ $A $P) => `(iprop(∀ᵣᵥ:$A , $P))

end LProp

/- Satisfaction relation: `(γ, D, Ω)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `Ω` -/
-- notation:50 "(" γ ", " D ", " Ω ")⊨ " P => Assertion.denote P γ D Ω

namespace Substitution

open Iris.ProofMode LProp Appl Iris.BI.BIBase

variable {ds rs rs' : List Ty} {A A' r : Ty}
-- ∀ X : RV ⟪r⟫, P.1 (γ, (X ; D)) Ω

abbrev substLProp (P : LProp ds (A::rs)) (X : RV ⟪A⟫) : LProp ds (rs) :=
  ⟨fun (γ, D) Ω ↦ P.1 (γ, X ; D) Ω, sorry⟩

/- There is a `def` of the same name in ProofRules.lean, which is used to define the congruence
lemma. There I incorrectly do a `drop` of a rv as well, so these definitions are different and that
definition is incorrect. Rectify that and the congruence lemma later. -/
-- abbrev substValRand (X : RV ⟪A⟫) (E : ValRand ds (A::rs) ⟪A'⟫) : ValRand ds rs ⟪A'⟫ :=
--   fun γ ↦ ⟨fun D ↦ (E γ (⟨X, D⟩ᶠ)), Measurable.prod (E γ).2 (measurable_id)⟩
  --∘ₘ ⟨Prod.snd, measurable_snd⟩

instance {P : LProp ds (r::rs)}
    : FromForall (forall_rv r P) (fun X : RV ⟪r⟫ ↦ substLProp P X) where
  from_forall := by
    rintro ⟨γ, D⟩ Ω P' X
    dsimp [Iris.BI.forall, sForall] at P'
    exact P' (substLProp P X) ⟨X, rfl⟩

instance {P : LProp ds (r::rs)}
    : IntoForall (forall_rv r P) (fun X : RV ⟪r⟫ ↦ substLProp P X) where
  into_forall := by
    rintro ⟨γ, D⟩ Ω P' P'' ⟨X, hX⟩
    subst hX
    simp only [P' X]

/- Since LProp couldn't be made an inductive structure, (due to a combination of iris-lean's forall
type) and lean's strict positivity in inductive types), we cannot prove the substituion lemma
through induction.
Note that the job of the "substitution lemma" is just to push cast-like functions such as
`substRandVar` into the `LProp` expression and all the way to the leaves.
Instead here we establish this same lemma through typeclasses and typeclass based proof search
(this technique is heavily exploited by Iris). Here's what's happening:
The "constructors" of `LProp` are just defs in Lean, and morally these still form a tree (though
there is no associated induction hypothesis). We write a substitution sub-lemma for each node of the
tree, and typeclass-based proof search will dynamically chain together the sublemmas from a node all
the way to the leaves to construct the substitution lemma for a given `Lprop` dynamically!
-/

class SubstRandProp (X : RV ⟪A⟫) (P : LProp ds (A::rs)) (Q : LProp ds rs) where
  subst_eq : substLProp P X = Q

instance (X : RV ⟪A⟫) (P Q : LProp ds (A::rs)) [SubstRandProp X P (substLProp P X)] [SubstRandProp X Q (substLProp P X)]
    : SubstRandProp X (iprop(P -∗ Q)) (iprop((substLProp P X) -∗ (substLProp Q X))) where
  subst_eq := rfl

/-- Leaf node of the substitution lemma. It seems like nothing can be done here due to `X : RV ⟪A⟫`
requiring an input from `HC` but E doesn't take that as input. -/
instance (E : ValRand ds (A::rs) ⟪A'⟫) (μ : DistDet ds ⟪A'⟫)
    : SubstRandProp X (LProp.dist E μ) (substLProp (LProp.dist E μ) X) where
  subst_eq := rfl

-- instance (X : RV ⟪A⟫) (P Q : LProp ds (A::rs)) [SubstRandProp X P (substLProp P X)] [SubstRandProp X Q (substLProp P X)]

-- def dist (E : ValRand ds rs ⟪A⟫) (μ : DistDet ds ⟪A⟫) : LProp ds rs :=


end Substitution
