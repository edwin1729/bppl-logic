/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Appl
import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules.WP

import Iris.ProofMode

/-! # Examples of proofs using the Iris proof mode instantiated to Lilac

- `unif1`: which samples from `unif01` in the language and shows the
corresponding result in the logic.
- `unif2`: like `unif1` but takes 2 independent samples `X` an `Y` and demonstrates
construction of a separating conjunct
- `half`: Given a random variable `X` in context and a uniform sample in [0,1], `Y`
  shows 𝔼[XY] = 𝔼[X]/2

-/

open LProp Appl Appl.Term Member Iris.BI ProbabilityTheory MeasurableFun WP RV
/-! There is still the unsolved problem of the programs being expressed via de brujin indices.
Maybe we can just have string based mapping somehow. -/
noncomputable section
-- Maybe use parametric abstract higher order syntax instead to make

abbrev nil : RV (List.TProd (⟪·⟫) []) :=
  ⟨⟨λ _ ↦ PUnit.unit, measurable_const⟩, RV.ff_const PUnit.unit⟩

notation "#0" => var head
notation "#1" => var (tail head)

namespace Unif1
-- abbrev post1 : LProp := wp (unif1.den ∘ᵣ nil) (λ X : RV ⟪Ty.real⟫ ↦ iprop(X ∼ unif01_sem))

abbrev unif1 : Term [] Ty.real.G :=
  unif01.bind (
  ret (#0)
)

lemma hrw {A : Ty} {X : RV ⟪A⟫} : ((#0).den ∘ᵣ (X ;; nil)) = X := by rfl

theorem unif1_spec :
    iprop(⊢ wp (unif1.den ∘ᵣ nil) (λ X : RV ⟪Ty.real⟫ ↦ iprop(X ∼ unif01_sem))) := by
  iapply wp_bind
  iapply wp_unif
  iintro %X HX
  iapply wp_ret
  rw [hrw]
  iexact HX

end Unif1

namespace Unif2

abbrev unif2 : Term [] (Ty.prod .real .real).G :=
  unif01.bind (
  unif01.bind (
  ret (pair (var (tail head)) (var head))
))

notation:10 D ".ₘ1" => (measurableFun_fst ∘ᵣ D)
notation:10 D ".ₘ2" => (measurableFun_snd ∘ᵣ D)

abbrev post2 : LProp := wp (unif2.den ∘ᵣ nil) (λ (Z : RV ⟪Ty.prod .real .real⟫) ↦
  iprop((Z.ₘ1) ∼ unif01_sem ∗ (Z.ₘ2) ∼ unif01_sem))

lemma hrw2₁ {A : Ty} (X Y : RV ⟪A⟫) :
  (measurableFun_fst ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = X := by rfl
lemma hrw2₂ {A : Ty} (X Y : RV ⟪A⟫) :
  (measurableFun_snd ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = Y := by rfl

theorem unif2_spec : iprop(⊢ post2) := by
  rw [post2]
  iintro
  iapply wp_bind
  iapply wp_unif
  iintro %X HX
  iapply wp_bind
  iapply wp_unif
  iintro %Y HY
  iapply wp_ret
  rw [hrw2₁, hrw2₂]
  isplitl [HX]
  · iexact HX
  · iexact HY

end Unif2

namespace Half

lemma expectation_of_own {X : RV ⟪Ty.real⟫} : own X ⊢ iprop(∃ e, 𝔼[X]=e) := by
  intro Ω ownX
  use iprop(𝔼[X]=∫ ω, X ω ∂(Ω.μ))
  simp only [exists_apply_eq_apply, true_and]
  exact ⟨ownX, rfl⟩

lemma expectation_prod {X Y : RV ⟪Ty.real⟫} {xy : ℝ} :
    iprop(∃ x y, 𝔼[X]=x ∧ 𝔼[Y]=y ∧ ⌜x * y = xy⌝) ⊢ iprop(𝔼[X * Y]=xy) := by
  intro Ω lhs

  sorry

#check ProbabilityTheory.IndepFun

-- NOTE: independence holds w.r.t. the *resource* measure `Ω.μ`, not the fixed global `lebHC`.
-- The `own X ∗ own Y` hypothesis only constrains the resource's own measure (via the independent
-- product `=ᵢ`), so the conclusion cannot mention `lebHC` (e.g. `X = Y = coordProj 0` with `Ω.μ`
-- a point mass satisfies the hypothesis but is not independent under `lebHC`).
open ProbabilityTheory in
lemma indep_of_own {X Y : RV ⟪Ty.real⟫} (Ω : PSp)
    (h : (iprop(own X ∗ own Y) : LProp).1 Ω) :
    IndepFun (_mΩ := Ω.ms) (μ := Ω.μ) X Y := by
  obtain ⟨σ₁, σ₂, σ₁₂, hle, hX, hY⟩ := h
  -- the underlying `PSpace`-level independent product
  have hval : σ₁.1 ⋆ σ₂.1 = some (↓σ₁₂).1 := by
    rw [PSp.psp_val_get σ₁ σ₂ σ₁₂, Option.some_get]
  have hindep := PSpace.Krm.isIndependentProduct_of_binop_eq_some hval
  -- `σ₁, σ₂ ≤ ↓σ₁₂ ≤ Ω`, so their measures all agree with `Ω.μ` on their σ-algebras
  have hle' : (↓σ₁₂).1 ≤ Ω.1 := hle
  have hp₁ : σ₁.1 ≤ Ω.1 := le_trans (PSpace.le_of_isIndependentProduct_left hindep) hle'
  have hp₂ : σ₂.1 ≤ Ω.1 := le_trans (PSpace.le_of_isIndependentProduct_right hindep) hle'
  refine (indepFun_iff_measure_inter_preimage_eq_mul).2 (fun s t hs ht => ?_)
  have hE : @MeasurableSet HC σ₁.ms (X ⁻¹' s) := hX hs
  have hF : @MeasurableSet HC σ₂.ms (Y ⁻¹' t) := hY ht
  have hfac : (↓σ₁₂).1.μ (X ⁻¹' s ∩ Y ⁻¹' t)
      = σ₁.1.μ (X ⁻¹' s) * σ₂.1.μ (Y ⁻¹' t) := hindep.2 _ hE _ hF
  have hEF : @MeasurableSet HC (↓σ₁₂).1.ms (X ⁻¹' s ∩ Y ⁻¹' t) := by
    rw [hindep.1]; exact mem_sum_inter _ _ hE hF
  have h1 : Ω.μ (X ⁻¹' s ∩ Y ⁻¹' t) = (↓σ₁₂).1.μ (X ⁻¹' s ∩ Y ⁻¹' t) :=
    (MeasureOnSpace.le_preserves_measure hle' hEF).symm
  have h2 : Ω.μ (X ⁻¹' s) = σ₁.1.μ (X ⁻¹' s) :=
    (MeasureOnSpace.le_preserves_measure hp₁ hE).symm
  have h3 : Ω.μ (Y ⁻¹' t) = σ₂.1.μ (Y ⁻¹' t) :=
    (MeasureOnSpace.le_preserves_measure hp₂ hF).symm
  rw [h1, h2, h3]; exact hfac

lemma expectation_of_unif01 {X : RV ⟪Ty.real⟫} : iprop(X ∼ unif01_sem ⊢ 𝔼[X]=0.5) := sorry

abbrev half : Term [Ty.real] Ty.real.G :=
  unif01.bind (
    ret (#1 * #0)
  )

-- abbrev X : RV ⟪Ty.real⟫ := ⟨⟨λ ω ↦ ω 0, sorry⟩, sorry⟩

abbrev envX : RV (List.TProd (⟪·⟫) [Ty.real]) := ⟨⟨λ ω ↦ (ω 0, PUnit.unit), sorry⟩, sorry⟩

abbrev post_half (X : RV ⟪Ty.real⟫) : LProp := wp (half.den ∘ᵣ (X ;; nil)) (λ Y : RV ℝ ↦
    iprop(∃ e, 𝔼[Y]=e/2 ∧ 𝔼[X]=e))

lemma hrw (X Y : RV ⟪Ty.real⟫) : ((arith Arith.mul #1 #0).den ∘ᵣ Y ;; X ;; nil) = X * Y := by rfl
lemma hr2 (X Y : RV ⟪Ty.real⟫) : ((arith Arith.mul #1 #0).den ∘ᵣ Y ;; X ;; nil)
  = ((Term.den ((#1 * #0): Term [Ty.real, Ty.real] Ty.real)) ∘ᵣ Y ;; X ;; nil) := by rfl

theorem half_spec (X : RV ⟪Ty.real⟫) : own X ⊢ post_half X := by
  iintro hX
  rw [post_half]
  iapply wp_bind
  iapply wp_unif
  iintro %Y hY
  iapply wp_ret
  rw [← hr2, hrw]
  ihave expX := expectation_of_own $$ hX
  icases expX with ⟨%e, he⟩
  iexists e
  isplit
  · iapply expectation_prod
    iexists e, 0.5
    ihave expY := expectation_of_unif01 $$ hY
    isplit
    · iexact he
    · isplit
      · iexact expY
      · ipure_intro
        ring
  · iexact he
  -- iexists (∫ ω, X ω ∂(Ω.μ))

end Half
