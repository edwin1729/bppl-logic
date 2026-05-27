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

open Appl MeasureTheory MeasureTheory.Measure ProbabilityTheory ProbabilityTheory.Kernel
open List (TProd)

open Iris.Instances.Intuitionistic Iris.Instances.Intuitionistic.instBIBase

/-- Lilac propositions -/
abbrev LProp := IProp PSp

-- Using `MeasurableSpace.pi`
instance : MeasurableSpace HC := inferInstance

namespace LProp

-- ds: deterministic context, rs: random variable context
variable {ds : List Ty} {rs : List Ty} {A : Ty}

def own (E : RV ⟪A⟫) : LProp :=
  ⟨fun Ω ↦ Measurable[Ω.ms] E, by
    intro σ₁ σ₂ hle hm
    exact hm.mono hle.1 le_rfl ⟩

def dist (E : RV ⟪A⟫) (μ : Measure ⟪A⟫) : LProp :=
  ⟨fun Ω ↦ Measurable[Ω.ms] E ∧ μ = Measure.bind Ω.μ (fun ω ↦ Measure.dirac (E ω)),
  -- monotonicity proof
  by
    intro σ₁ σ₂ hle ⟨hm, hbind⟩
    change σ₁.toPSpace ≤ σ₂.toPSpace at hle
    obtain ⟨hms, hmu⟩ := hle
    refine ⟨hm.mono hms le_rfl, ?_⟩
    rw [hbind, hmu,
        Measure.bind_dirac_eq_map _ (hm.mono hms le_rfl),
        Measure.bind_dirac_eq_map _ hm,
        Measure.cast_eq_self,
        Measure.map_map hm (measurable_id.mono hms le_rfl)]
    rfl
  ⟩

def expectation (E : RV ⟪Ty.real⟫) (e : ℝ) : LProp :=
  ⟨fun Ω ↦ Measurable[Ω.ms] E ∧ ∫ ω, E ω ∂(Ω.μ) = e, sorry⟩

-- We do not use `ae` filter and general mathlib infrastructure, because these don't give the
-- very particular measurability of spaces that we require
def eq (E₁ E₂ : RV ⟪A⟫) : LProp :=
  ⟨fun ⟨⟨⟨ℱ, μ⟩, hμ⟩, _⟩ ↦
    let F := {ω | E₁ ω = E₂ ω}
    MeasurableSet[ℱ] F ∧ μ F = 1 ∧
    -- (F ∪ ⟨X₁, X₂⟩ᶠ⁻¹' ·) '' (⟪A⟫ᵐ.prod ⟪A⟫ᵐ).MeasurableSet' ⊆ ℱ.MeasurableSet'
    ∀ x :Set (⟪A⟫ × ⟪A⟫), MeasurableSet x →
      MeasurableSet[ℱ] (F ∪ (fun ω ↦ (E₁ ω, E₂ ω))⁻¹' x),
    -- monotonicity proof
    by
    intro σ₁ σ₂ hle ⟨hF_meas, hF_prob, hF_union⟩
    change σ₁.toPSpace ≤ σ₂.toPSpace at hle
    obtain ⟨hms, hmu⟩ := hle
    refine ⟨hms _ hF_meas, ?_, fun x hx => hms _ (hF_union x hx)⟩
    rw [hmu] at hF_prob
    rwa [Measure.map_apply (measurable_id.mono hms le_rfl) hF_meas, Set.preimage_id] at hF_prob
  ⟩

def PSpace.mk' {Ω : Type*} {ms : MeasurableSpace Ω} (μ : ProbabilityMeasure Ω) : PSpace Ω :=
  ⟨⟨_, μ.1⟩, μ.2⟩

noncomputable abbrev det [MeasurableSpace α] (X : RV α) : Kernel HC α  :=
  deterministic X X.meas

open HC in
def wp (M : RV (⟪Ty.G A⟫)) (Q : RV ⟪A⟫ → LProp) : LProp :=
  ⟨fun Ω ↦
  ∀ Ω_fr : PSp, ∀ Ω_pre : ✓'(Ω_fr ⋆ Ω), ∀ μ : @ProbabilityMeasure HC Inf_borel,
    (↓Ω_pre).1 ≤ PSpace.mk' μ → ∀ {α: Type} {msα : MeasurableSpace α} (D_ext : RV α),
  ∃ X : RV ⟪A⟫, ∃ Ω' : PSp, ∃ Ω_post: ✓'(Ω_fr ⋆ Ω'), ∃ μ' : @ProbabilityMeasure HC Inf_borel,
    (↓Ω_post).1 ≤ PSpace.mk' μ' ∧
  -- (μ.1.bind (fun ω ↦ (M ω).bind (fun v ↦ Measure.dirac (D ω, v)))) =
  --   (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D ω, X ω))) ∧
  (toMK M ×ₖ det D_ext) ∘ₘ μ = (det X ×ₖ det D_ext) ∘ₘ μ' ∧
  (Q X).1 Ω'
  ,
  -- monotonicity proof
  by
  intro σ₁ σ₂ hle hσ₁ Ω_fr Ω_pre μ hpre_le _ _ D
  -- From σ₁ ≤ σ₂ and ✓'(Ω_fr ⋆ σ₂), get ✓'(Ω_fr ⋆ σ₁) with ↓ ≤ ↓
  obtain ⟨Ω_pre₁, hle_pre⟩ := KrmHelper.le_mul_mono_right' hle Ω_pre
  have hpre_le' : (↓Ω_pre₁).toPSpace ≤ PSpace.mk' μ :=
    (show (↓Ω_pre₁).toPSpace ≤ (↓Ω_pre).toPSpace from hle_pre).trans hpre_le
  exact hσ₁ Ω_fr Ω_pre₁ μ hpre_le' D
  ⟩

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

syntax:53 " 𝔼[ " term:52 " ]= " term:54 : term

macro_rules
  | `(iprop(𝔼[$E]=$e)) => `(expectation $E $e)

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
