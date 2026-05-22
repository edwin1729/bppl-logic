/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Assertion
import Bppl.Lilac.MeasureProduct
import Bppl.Lilac.WPUnifHelpers

namespace WP
open Appl PMF NNReal List ProbabilityTheory ProbabilityTheory.Kernel MeasureTheory.Measure
open Iris.BI.BIBase LProp Iris.BI
-- importing all of MeasureTheory imports an operator ∗ conflicting with the separating conjunct
open MeasureTheory (Measure ProbabilityMeasure)
variable {ds : List Ty} {rs : List Ty} {r r' : Ty} {A B ty₁ ty₂ : Ty}
noncomputable section

abbrev ret [MeasurableSpace α] (a : α) := dirac a

-- Appendix B.20
lemma wp_cons {P Q : RV ⟪A⟫ → LProp} {M : RV (ProbabilityMeasure ⟪A⟫)}
    (P_entails_Q : ∀ X : RV ⟪A⟫, iprop(P X ⊢ Q X)) : iprop(wp M P ⊢ wp M Q) := by
  intro Ω wp_l Ω_fr μ hΩ
  sorry

open KrmHelper in
lemma wp_frame {F : LProp} {Q : RV ⟪A⟫ → LProp} {M : RV (ProbabilityMeasure ⟪A⟫)} :
    iprop(F ∗ (wp M Q) ⊢ wp M (fun X ↦ iprop(F ∗ Q X))) := by
  rintro Ω ⟨Ω_F, Ω_M, Ω_F_M, hΩ_F_M,  hF, wp_left⟩ Ω_fr Ω_fr_Ω μ hΩ_fr_Ω _ _ D_ext
  -- all the shuffling paranthesis needed to feed arguments into `wp_left`
  obtain ⟨Ω_fr_F_M, hΩ_fr_F_M⟩ := le_mul_mono_right' hΩ_F_M Ω_fr_Ω
  have Ω_fr_F_M_le_μ : (↓(assoc_left Ω_fr_F_M)).toPSpace ≤ PSpace.mk' μ := by
    trans (↓Ω_fr_Ω).toPSpace
    · rw [assoc_left_eq Ω_fr_F_M]
      exact hΩ_fr_F_M
    · exact hΩ_fr_Ω
  obtain ⟨X, Ω_M', Ω_fr_F_M', μ', Ω_fr_F_M'_le_μ', calc_block, post_left_wp⟩ :=
    wp_left ↓(left Ω_fr_F_M) (assoc_left Ω_fr_F_M) μ Ω_fr_F_M_le_μ D_ext
  -- and now feed these "outputs" from `wp_left` into wp_right (the goal).
  refine ⟨X, ↓(right Ω_fr_F_M'), (assoc_right Ω_fr_F_M'), μ', ?le_μ', calc_block, ?post_right_wp⟩
  case le_μ' =>
    exact (assoc_right_eq Ω_fr_F_M').symm ▸ Ω_fr_F_M'_le_μ'
  case post_right_wp =>
    use Ω_F, Ω_M', (right Ω_fr_F_M')

lemma wp_disj {P Q : RV ⟪A⟫ → LProp} {M : RV (ProbabilityMeasure ⟪A⟫)} :
    iprop((wp M P) ∨ (wp M Q) ⊢ wp M (fun X ↦ iprop(P X ∨ Q X))) := sorry

-- Appendix B.22 from Lilac paper
-- TODO: It is unclear how to express the substitution of `wp_ret`. Just a function?

lemma wp_ret (Q : RV ⟪A⟫ → LProp) (D : RV (TProd (⟪·⟫) rs)) (M : Term rs A) :
    iprop((Q (M.den ∘ᵣ D)) ⊢ wp ((Term.ret M).den ∘ᵣ D) Q) := by
  rintro Ω wp Ω_fr Ω_pre μ Ω_pre_le_μ _ _ D_ext
  use (M.den ∘ᵣ D), Ω, Ω_pre, μ, Ω_pre_le_μ
  exact ⟨rfl, wp⟩

variable [MeasurableSpace α] [MeasurableSpace β]
/-- helper needed since we use `RV` instead of as a wrapper around measurable functions. -/
lemma h_det_prod (f : RV α) (g : RV β) : det f ×ₖ det g = det (f ;; g) :=
          Kernel.deterministic_prod_deterministic f.meas g.meas

lemma wp_bind (Q : RV ⟪B⟫ → LProp) (D : RV (TProd (⟪·⟫) rs))
    (M : Term rs A.G) (N : Term (A::rs) B.G)
    : wp (M.den ∘ᵣ D) (fun X ↦ (wp (N.den ∘ᵣ (X ;; D)) Q)) ⊢ wp ((M.bind N).den ∘ᵣ D) Q := by
  rintro Ω wp_outer Ω_fr Ω_pre μ Ω_pre_le_μ _ _ D_ext
  obtain ⟨X, Ω_X, Ω_fr_X, μX, Ω_fr_X_le_μX, calc_outer, wp_inner⟩ :=
    wp_outer Ω_fr Ω_pre μ Ω_pre_le_μ (D ;; D_ext)
  obtain ⟨Y, Ω_Y, Ω_fr_Y, μY, Ω_fr_Y_le_μY, calc_inner, post_cond⟩ :=
    wp_inner Ω_fr Ω_fr_X μX Ω_fr_X_le_μX D_ext
  refine ⟨Y, Ω_Y, Ω_fr_Y, μY, Ω_fr_Y_le_μY, ?calc_left, post_cond⟩
  calc
    -- unfold denotation of syntactic bind into semantic bind
    _ = ((Kernel.comap (toMK (M.bind N).den) D D.meas) ×ₖ det D_ext) ∘ₘ μ := by rfl
    _ = (((toMK N.den) ∘ₖ (toMK M.den ×ₖ Kernel.id)).comap D.toFun D.meas ×ₖ det D_ext) ∘ₘ μ := by
      rfl
    _ = (((toMK N.den) ∘ₖ (toMK M.den ×ₖ Kernel.id).comap D.toFun D.meas) ×ₖ det D_ext) ∘ₘ μ := by
      rfl
    _ = ((toMK N.den ∥ₖ Kernel.id) ∘ₖ ((toMK M.den ×ₖ Kernel.id).comap D.toFun D.meas ×ₖ det D_ext))
            ∘ₘ μ := by
        -- We know that it `IsSFinite`, since `M.den`, `IsMarkovKernel`
        haveI : IsSFiniteKernel ((toMK M.den ×ₖ Kernel.id).comap D.toFun D.meas) :=
          Kernel.IsSFiniteKernel.comap _ D.meas
        rw [Kernel.parallelComp_comp_prod, Kernel.id_comp]
    _ = (toMK N.den ∥ₖ Kernel.id) ∘ₘ (((toMK M.den ×ₖ Kernel.id).comap D.toFun D.meas ×ₖ det D_ext)
            ∘ₘ μ) := Measure.comp_assoc.symm
    _ = (toMK N.den ∥ₖ Kernel.id) ∘ₘ ((((toMK M.den).comap D D.meas ×ₖ det D) ×ₖ det D_ext) ∘ₘ μ) :=
      by rw [Kernel.comap_prod, Kernel.id_comap]; rfl
    _ = (toMK N.den ∥ₖ Kernel.id) ∘ₘ (((det X ×ₖ det D) ×ₖ det D_ext) ∘ₘ μX) := by
        suffices h_inner :
            ((((toMK M.den).comap D D.meas ×ₖ det D) ×ₖ det D_ext) ∘ₘ μ) =
              (((det X ×ₖ det D) ×ₖ det D_ext) ∘ₘ μX) by
          rw [h_inner]
        have h_det_prod : det D ×ₖ det D_ext = det (D ;; D_ext) :=
          Kernel.deterministic_prod_deterministic D.meas D_ext.meas
        -- assoc yields an additional `.map prodAssoc.symm` like
        -- `(A ×ₖ B) ×ₖ C = (A ×ₖ (B ×ₖ C)).map prodAssoc.symm` on both sides
        -- push the `.map` through `∘ₘ μ`, then reduce to `calc_outer`.
        rw [← Kernel.prodAssoc_symm_prod ((toMK M.den).comap D D.meas) (det D_ext) (det D),
            ← Kernel.prodAssoc_symm_prod (det X) (det D_ext) (det D),
            ← Measure.map_comp _ _ MeasurableEquiv.prodAssoc.symm.measurable,
            ← Measure.map_comp _ _ MeasurableEquiv.prodAssoc.symm.measurable]
        congr 1
        rw [h_det_prod]
        exact calc_outer
    _ = ((toMK N.den ∥ₖ Kernel.id) ∘ₖ ((det X ×ₖ det D) ×ₖ det D_ext)) ∘ₘ μX := Measure.comp_assoc
    _ = (((toMK N.den) ∘ₖ (det X ×ₖ det D)) ×ₖ det D_ext) ∘ₘ μX  := by
        haveI : IsSFiniteKernel (det X ×ₖ det D) := inferInstance
        rw [Kernel.parallelComp_comp_prod, Kernel.id_comp]
    _ = (det Y ×ₖ det D_ext) ∘ₘ μY := by
        -- Compose `det X ×ₖ det D = det (X ;; D)` with `K ∘ₖ deterministic g = comap K g`
        -- to identify the LHS kernel with `toMK (N.den ∘ᵣ (X ;; D))`, then `calc_inner`.
        convert calc_inner
        change toMK N.den ∘ₖ (deterministic X.toFun X.meas ×ₖ deterministic D.toFun D.meas)
          = toMK (N.den ∘ᵣ X ;; D).toMeasurableFun
        rw [Kernel.deterministic_prod_deterministic X.meas D.meas]
        exact Kernel.comp_deterministic_eq_comap (toMK N.den) (X ;; D).meas

end
end WP
