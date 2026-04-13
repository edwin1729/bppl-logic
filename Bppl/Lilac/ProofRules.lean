/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Iris.BI.BIBase
import Iris.BI
import Iris.BI.Classes
import Iris.ProofMode

import Bppl.Lilac.Assertion

set_option autoImplicit true
set_option relaxedAutoImplicit true


open Iris.BI.BIBase LProp Iris.BI Appl.Denotation
/- Almost Surely EQual-/
namespace Aseq
open MeasurableSpace

variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]
{ds : List TyDet} {rs : List TyRand} {A : TyRand}

namespace helper
-- move to a measure theory helper file
open MeasureTheory in
/-- An equivalent way of stating the measurability condition of `≗`.  We require `MeasureableEq`
spaces just to satisfy this lemma, which is then required to prove transitivity of `≗`.
Appendix B.12 from Lilac paper -/
lemma aseq_measurable_alt {α β : Type*} [msα : MeasurableSpace α] [msβ : MeasurableSpace β]
      [MeasurableEq β] {F : Set α} (hF : MeasurableSet F) (X₁ X₂ : α → β)
    : List.TFAE [
      ∀ x : Set (β × β), MeasurableSet[msβ.prod msβ] x → MeasurableSet (F ∪ ⟨X₁, X₂⟩ᶠ⁻¹' x),
      -- ∀ x : Set (β × β), MeasurableSet[msβ.prod msβ] x → MeasurableSet (Fᶜ ∩ ⟨X₁, X₂⟩ᶠ⁻¹' x),
      (F ∪ ⟨X₁, X₂⟩ᶠ⁻¹' ·) '' (msβ.prod msβ).MeasurableSet' ⊆ msα.MeasurableSet',
      (F ∪ X₁⁻¹' ·) '' msβ.MeasurableSet' ⊆ msα.MeasurableSet' ∧
      (F ∪ X₂⁻¹' ·) '' msβ.MeasurableSet' ⊆ msα.MeasurableSet',
      (Fᶜ ∩ X₁⁻¹' ·) '' msβ.MeasurableSet' ⊆ msα.MeasurableSet' ∧
      (Fᶜ ∩ X₂⁻¹' ·) '' msβ.MeasurableSet' ⊆ msα.MeasurableSet',

    ] := by
      tfae_have 1 → 3 := by sorry
      sorry

open MeasureTheory in
/-- Appendix B.14 from Lilac paper -/
lemma full_set_measure_eq_zero_or_one {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α)
    {E : Set α} (hE : MeasurableSet[generateFrom {x | μ x = 1}] E)
    : μ E = 1 ∨ μ E = 0 := by sorry

end helper

abbrev fProd {α β γ : Type*} (f : α → β) (g : α → γ) (x : α) : β × γ := (f x, g x)
notation " ⟨ " f ", " g " ⟩ᶠ " => fProd f g
/-- Appendix B.13 from Lilac paper -/
lemma refl (E₁ : ValRand ds rs A) : iprop( ⊢ E₁ ≗ E₁) := by
  rintro ⟨γ, D⟩ ⟨⟨ℱ, μ⟩, is_prob⟩ _
  simp [eq]
/-- Appendix B.13 from Lilac paper -/
lemma symm (E₁ E₂ : ValRand ds rs A) : iprop(E₁ ≗ E₂ ⊢ E₂ ≗ E₁) := by
  rintro ⟨γ, D⟩ ⟨⟨ℱ, μ⟩, is_prob⟩ eq_l
  dsimp [eq] at ⊢ eq_l
  obtain ⟨h₁, h₂, h_meas_union⟩ := eq_l
  have symm_full_set : {ω | E₁ γ (D ω) = E₂ γ (D ω)} = {ω | E₂ γ (D ω) = E₁ γ (D ω)} :=
      by ext; exact ⟨Eq.symm, Eq.symm⟩
  constructor
  · rwa [← symm_full_set]
  · constructor
    · rwa [← symm_full_set]
    · intro x hx
      have h_meas_union_swap := h_meas_union (Prod.swap ⁻¹' x) (measurableSet_swap_iff.2 hx)
      have h_prod_swap :
          (fun ω ↦ (E₁ γ (D ω), E₂ γ (D ω))) ⁻¹' (Prod.swap ⁻¹' x) =
          (fun ω ↦ (E₂ γ (D ω), E₁ γ (D ω))) ⁻¹' x
        := by ext; simp
      rw [h_prod_swap, symm_full_set] at h_meas_union_swap
      exact h_meas_union_swap

/-- Appendix B.13 from Lilac paper -/
lemma trans (E₁ E₂ E₃ : ValRand ds rs A) : iprop(E₁ ≗ E₂ ∧ E₂ ≗ E₃ ⊢ E₁ ≗ E₃) := by
  rintro ⟨γ, D⟩ ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨⟨meas_F₁₂, full_F₁₂, hF₁₂⟩, ⟨meas_F₂₃, full_F₂₃, hF₂₃⟩⟩
  let X₁ := (E₁ γ) ∘ D
  let X₂ := (E₂ γ) ∘ D
  let X₃ := (E₃ γ) ∘ D
  let F₁₃ := {ω | X₁ ω = X₃ ω}

  have meas_F₁₃ : MeasurableSet F₁₃ := by sorry
  have full_F₁₃ : μ F₁₃ = 1 := by sorry
  have hF₁₃ : ∀ (x : Set (⟪A⟫ × ⟪A⟫)), MeasurableSet x → MeasurableSet (F₁₃ ∪ ⟨X₁, X₃⟩ᶠ⁻¹' x) := by
    sorry
  exact ⟨meas_F₁₃, full_F₁₃, hF₁₃⟩

-- Appendix B.15 from Lilac paper
lemma and_aseq_iff_sep_aseq (P : LProp ds rs) (E₁ E₂ : ValRand ds rs A) :
    iprop(P ∧ (E₁ ≗ E₂) ⊣⊢ P ∗ (E₁ ≗ E₂)) :=
  sorry

-- Maybe the definition of persistently could be changed inspired by the requirements of
-- this proof obligation
/-- Appendix B.16 from Lilac paper -/
instance aseq_persisitent (E₁ E₂ : ValRand ds rs A) : Persistent iprop(E₁ ≗ E₂) where
  persistent := sorry

/-- Appendix B.17 from Lilac paper -/
lemma transfer_own (E₁ E₂ : ValRand ds rs A) : iprop(own E₁ ∧ E₁ ≗ E₂ ⊢ own E₂) := by
  rintro ⟨γ, D⟩ ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_own, h_eq⟩
  dsimp [own] at h_own ⊢
  dsimp [eq] at h_eq
  obtain ⟨h_meas_F, _, h_prod⟩ := h_eq
  let F := {ω | (E₁ γ) (D ω) = (E₂ γ) (D ω)}
  let X₁ : HC → ⟪A⟫ := fun ω ↦ (E₁ γ) (D ω)
  let X₂ : HC → ⟪A⟫ := fun ω ↦ (E₂ γ) (D ω)
  -- Goal: Measurable X₂
  change Measurable X₂
  intro S hS
  -- Step 1: F ∪ X₂⁻¹' S is measurable
  have h1 : MeasurableSet (F ∪ X₂ ⁻¹' S) := by
    have := h_prod (Set.univ ×ˢ S) (MeasurableSet.univ.prod hS)
    convert this using 1
    ext ω; simp [Set.mem_preimage, Set.mem_prod, fProd, F, X₂]
  -- Step 2: Fᶜ ∩ X₂⁻¹' S is measurable
  have h2 : MeasurableSet (Fᶜ ∩ X₂ ⁻¹' S) := by
    have : Fᶜ ∩ X₂ ⁻¹' S = (F ∪ X₂ ⁻¹' S) \ F := by
      ext ω; simp [Set.mem_diff, Set.mem_compl_iff, Set.mem_inter_iff]; tauto
    rw [this]; exact h1.diff h_meas_F
  -- Step 3: F ∩ X₂⁻¹' S = F ∩ X₁⁻¹' S is measurable
  have h3 : MeasurableSet (F ∩ X₂ ⁻¹' S) := by
    have hFeq : F ∩ X₂ ⁻¹' S = F ∩ X₁ ⁻¹' S := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, F, X₁, X₂,
                 Function.comp]
      constructor
      · rintro ⟨heq, hmem⟩; exact ⟨heq, heq ▸ hmem⟩
      · rintro ⟨heq, hmem⟩; exact ⟨heq, heq.symm ▸ hmem⟩
    rw [hFeq]; exact h_meas_F.inter (h_own hS)
  -- Step 4: X₂⁻¹' S = (F ∩ X₂⁻¹' S) ∪ (Fᶜ ∩ X₂⁻¹' S)
  have h4 : X₂ ⁻¹' S = (F ∩ X₂ ⁻¹' S) ∪ (Fᶜ ∩ X₂ ⁻¹' S) := by
    ext ω; simp [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  rw [h4]; exact h3.union h2

/-- Appendix B.17 from Lilac paper -/
lemma transfer_dist (E₁ E₂ : ValRand ds rs A) (ν : DistDet ds A) :
    iprop(E₁ ∼ ν ∧ E₁ ≗ E₂ ⊢ E₂ ∼ ν) := by
  rintro ⟨γ, D⟩ ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_dist, h_aseq⟩
  dsimp [LProp.dist] at h_dist ⊢
  dsimp [LProp.eq] at h_aseq
  obtain ⟨h_meas_X₁, h_eq_dist⟩ := h_dist
  obtain ⟨h_meas_F, h_full_F, h_prod⟩ := h_aseq
  constructor
  · -- Measurability of X₂: same proof as transfer_own
    exact (transfer_own E₁ E₂ (γ, D) ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_meas_X₁, h_meas_F, h_full_F, h_prod⟩ : (own E₂).1 (γ, D) ⟨⟨ℱ, μ⟩, is_prob⟩)
  · -- Distribution equality: since X₁ = X₂ a.e., Measure.bind μ (dirac ∘ X₁) = Measure.bind μ (dirac ∘ X₂)
    rw [h_eq_dist]
    -- bind μ f = (map f μ).join, so it suffices to show map f₁ = map f₂
    simp only [MeasureTheory.Measure.bind]
    congr 1
    apply MeasureTheory.Measure.map_congr
    -- Need: (fun ω ↦ dirac (X₁ ω)) =ᵐ[μ] (fun ω ↦ dirac (X₂ ω))
    -- Use Filter.EventuallyEq and show the set where they differ has measure 0
    have h_ae : ∀ᵐ ω ∂μ, (E₁ γ) (D ω) = (E₂ γ) (D ω) := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null
      · intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; exact hω
      · -- {ω | (E₁ γ)(D ω) ≠ (E₂ γ)(D ω)} has measure 0
        -- since its complement is F with μ F = 1
        convert MeasureTheory.measure_compl h_meas_F _ using 1 <;> aesop
    filter_upwards [h_ae] with ω hω
    rw [hω]

-- TODO B.18 what does `own(F[E₁], F[E₂])` mean in the paper?

-- B.19, don't think this is needed

-- Appendix B.22 from Lilac paper

end Aseq
namespace WP
open ProbabilityTheory MeasureTheory Appl PMF NNReal
-- variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]
variable {ds : List Ty} {rs : List Ty} {A ty₁ ty₂ : Ty}
noncomputable section

-- TODO: It is unclear how to express the substitution of `wp_ret`. Just a function?

/-- The semantic (native lean) uniform distribution in the interval [0,1]. -/
def unif01_sem : HList (⟪·⟫) ds → Measure ℝ := fun _ ↦ uniformOn (Set.Icc 0 1)

def ber_sem (p : ℝ≥0) (hp : p ≤ 1) : HList (⟪·⟫) ds → Measure Bool :=
  fun _ ↦ (bernoulli p hp).toMeasure

/-- Variable at the head of the random environment list. -/
def fst_rand : ValRand ds (A::rs) A :=
  fun _d_env ↦ ⟨fun r_env ↦ r_env.get .head , List.TProd.measurable_get .head⟩

lemma wp_unif (Q : LProp ds (Ty.real :: rs)) :
    forall_rv Ty.real iprop(fst_rand ∼ unif01_sem -∗ Q) ⊢ wp ⦃Term.unif01⦄ Q :=
  sorry

lemma wp_flip (p : ℝ≥0) (hp : p ≤ 1) (Q : LProp ds (Ty.bool :: rs)) :
    forall_rv Ty.bool iprop(fst_rand ∼ (ber_sem p hp) -∗ Q) ⊢ wp ⦃Term.flip p hp⦄ Q :=
  sorry

-- lemma wp_let (M : Term rs (.G ty₁)) (N : Term (ty₁ :: rs) (.G ty₂))
-- Term ctx (.G ty₁) → Term (ty₁ :: ctx) (.G ty₂) → Term ctx (.G ty₂)

end
end WP
