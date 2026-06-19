/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Bppl.Lilac.Appl
import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules.WP
import Iris.ProofMode

/-! # Proof Rules and Tactics on expectations

This file providesas a tactic `iexpect_prod`.

## The problem

We want to rewrite a goal `𝔼[X * Y] = xy` into `∃ x y, 𝔼[X]=x ∧ 𝔼[Y]=y ∧ x*y=xy`.
That rewrite is only sound when `X` and `Y` are independent.  In Lilac, independence is
*derived* from owning the two variables separately (`indep_of_own`). But the independence
fact `IndepFun (μ := Ω.μ) X Y` is *resource-specific* (it mentions `Ω.μ`),
so it cannot be embedded into an LProp.

## The solution (metaprogramming)

An iris entailment `e ⊢ goal` unfolds, in this model, to `∀ Ω, e.1 Ω → goal.1 Ω`.
`intro Ω he`, then the proof `he : e.1 Ω` is an ordinary `Prop`, he freely-reusable.

* project `OwnLike X ∗ Ownlike Y` out of `he` and feed it to `indep_of_own'` to obtain
  `IndepFun (μ := Ω.μ) X Y`, and
* feed `he` to a proof of the reduced goal `e ⊢ goal'`.

`expectation_prod_keep` - descending into meta logic; `proj_of_frame` packages the affine
projection.  The tactic only has to (a) locate the two kept hypotheses, (b) recover the framing
equivalences, and (c) emit the reduced goal with the **unchanged** context `hyps`.
-/

open LProp Appl Iris.BI

noncomputable section

namespace Lilac

/-- Affine projection of two separated factors out of a context, used to witness that the two
kept hypotheses are present.  Stated at `LProp` so the `BIAffine` instance resolves here, once. -/
theorem proj_of_frame {e eX eY oX oY : LProp}
    (pfX : e ⊣⊢ iprop(eX ∗ oX)) (pfY : eX ⊣⊢ iprop(eY ∗ oY)) :
    e ⊢ iprop(oX ∗ oY) :=
  pfX.1.trans <| (sep_mono_l (pfY.1.trans sep_elim_r)).trans sep_comm.1

/-- Model-level core: independence turns the factored expectation goal into the product goal -/
theorem expectation_prod {X Y : RV ⟪Ty.real⟫} {xy : ℝ} (Ω : PSp)
    (hindep : ProbabilityTheory.IndepFun (_mΩ := Ω.ms) (μ := Ω.μ) X Y)
    (hg : (iprop(∃ x y, 𝔼[X]=x ∧ 𝔼[Y]=y ∧ ⌜x * y = xy⌝) : LProp).1 Ω) :
    (iprop(𝔼[X * Y]=xy) : LProp).1 Ω := by
  -- Unfold the iris `∃`/`∧`/`⌜⌝` connectives in the model.
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, ⟨hmX, hiX⟩, ⟨hmY, hiY⟩, hxy⟩ := hg
  -- `X * Y` is measurable since `X` and `Y` are (w.r.t. the resource σ-algebra).
  refine ⟨hmX.mul hmY, ?_⟩
  -- `(X * Y) ω = X ω * Y ω` definitionally, so independence factors the integral.
  change ∫ ω, X ω * Y ω ∂Ω.μ = xy
  rw [hindep.integral_fun_mul_eq_mul_integral hmX.aestronglyMeasurable hmY.aestronglyMeasurable,
    hiX, hiY]
  exact hxy

-- Generalises `indep_of_own` from `own` to any pair of `OwnLike` assertions (`own`, `dist μ`,
-- `expectation e`): independence (w.r.t. the resource measure `Ω.μ`) follows from a separating
-- conjunction of resource-measurability facts, regardless of what else the assertions claim.
open ProbabilityTheory in
lemma indep_of_own' {A B : Ty} {X : RV ⟪A⟫} {Y : RV ⟪B⟫} (Ω : PSp)
    (sertX : RV ⟪A⟫ → LProp) (sertY : RV ⟪B⟫ → LProp)
    [OwnLike A sertX] [OwnLike B sertY]
    (ownXY : (iprop(sertX X ∗ sertY Y) : LProp).1 Ω) :
    IndepFun (_mΩ := Ω.ms) (μ := Ω.μ) X Y := by
  obtain ⟨σ₁, σ₂, σ₁₂, hle, hsX, hsY⟩ := ownXY
  -- extract resource-measurability from the `OwnLike` assertions
  have hX : @Measurable HC ⟪A⟫ σ₁.ms _ X := OwnLike.meas X σ₁ hsX
  have hY : @Measurable HC ⟪B⟫ σ₂.ms _ Y := OwnLike.meas Y σ₂ hsY
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

/-- Apply `expectation_prod` while keeping the premises -/
theorem expectation_prod_keep {X Y : RV ⟪Ty.real⟫} {xy : ℝ}
    (sertX sertY : RV ⟪Ty.real⟫ → LProp)
    [OwnLike Ty.real sertX] [OwnLike Ty.real sertY]
    {e eX eY : LProp}
    (pfX : e ⊣⊢ iprop(eX ∗ sertX X)) (pfY : eX ⊣⊢ iprop(eY ∗ sertY Y))
    (hgoal : e ⊢ iprop(∃ x y, 𝔼[X]=x ∧ 𝔼[Y]=y ∧ ⌜x * y = xy⌝)) :
    e ⊢ iprop(𝔼[X * Y]=xy) := by
  have proj := proj_of_frame pfX pfY
  intro Ω he
  exact expectation_prod Ω (indep_of_own' Ω sertX sertY (proj Ω he)) (hgoal Ω he)

end Lilac

section Tactic
open Lean Elab Tactic Meta Qq
open Iris.ProofMode Iris.BI

/-- `iexpect_prod H1 H2` : with `H1 : sertX X` and `H2 : sertY Y` (any two `OwnLike` spatial
hypotheses) present in the spatial context, reduce a goal
`𝔼[X * Y] = xy` to `∃ x y, 𝔼[X]=x ∧ 𝔼[Y]=y ∧ ⌜x*y=xy⌝`.

The hypotheses `H1` and `H2` are kept in the resulting context. -/
elab "iexpect_prod" h1:ident h2:ident : tactic => do
  ProofModeM.runTactic fun mvar g => do
    let { hyps, goal, .. } := g
    -- The goal must be `𝔼[_ * _] = xy`; we only need `xy` from it.
    let_expr LProp.expectation xy _E := goal |
      throwError "iexpect_prod: goal is not of the form 𝔼[_ * _] = _"
    have xy : Q(ℝ) := xy
    -- Locate the two hypotheses by name (read-only: this does NOT remove them).
    let uniqX ← hyps.findWithInfo h1
    let uniqY ← hyps.findWithInfo h2
    -- Use `remove` purely to recover clean hypothesis types and framing equivalences;
    -- the resulting `hyps` are discarded — we keep the original `hyps`.
    let ⟨_eX, hypsX, _outX, tyX, pX, _, pfX⟩ := hyps.remove false uniqX
    let ⟨_eY, _hypsY, _outY, tyY, pY, _, pfY⟩ := hypsX.remove false uniqY
    unless (isTrue pX == false && isTrue pY == false) do
      throwError "iexpect_prod: both hypotheses must be spatial (not intuitionistic)"
    -- Recover `sertX, X` and `sertY, Y` from the (bare) hypothesis types `sertX X`, `sertY Y`.
    have X     : Q(RV ⟪Ty.real⟫)          := tyX.appArg!
    have sertX : Q(RV ⟪Ty.real⟫ → LProp)  := tyX.appFn!
    have Y     : Q(RV ⟪Ty.real⟫)          := tyY.appArg!
    have sertY : Q(RV ⟪Ty.real⟫ → LProp)  := tyY.appFn!
    -- Emit the reduced goal with the unchanged context `hyps`.
    let goal' : Q(LProp) := q(iprop(∃ x y, 𝔼[$X]=x ∧ 𝔼[$Y]=y ∧ ⌜x * y = $xy⌝))
    let hgoal ← addBIGoal hyps goal' (← mvar.getTag)
    -- The framing equivalences `pfX, pfY` and the reduced-goal proof `hgoal` are handed to the
    -- `expectation_prod_keep`.
    let pf ← mkAppM ``Lilac.expectation_prod_keep #[sertX, sertY, pfX, pfY, hgoal]
    mvar.assign pf

end Tactic

lemma expectation_of_own {X : RV ⟪Ty.real⟫} : own X ⊢ iprop(∃ e, 𝔼[X]=e) := by
  intro Ω ownX
  use iprop(𝔼[X]=∫ ω, X ω ∂(Ω.μ))
  simp only [exists_apply_eq_apply, true_and]
  exact ⟨ownX, rfl⟩

open ProbabilityTheory in
lemma indep_of_own {X Y : RV ⟪Ty.real⟫} (Ω : PSp)
    (ownXY : (iprop(own X ∗ own Y) : LProp).1 Ω) :
    IndepFun (_mΩ := Ω.ms) (μ := Ω.μ) X Y := by
  obtain ⟨σ₁, σ₂, σ₁₂, hle, hX, hY⟩ := ownXY
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

open MeasureTheory in
lemma expectation_of_unif01 {X : RV ⟪Ty.real⟫} : iprop(X ∼ unif01_sem ⊢ 𝔼[X]=0.5) := by
  intro Ω h
  -- `X ∼ unif01_sem` gives measurability plus `unif01_sem = X_* Ω.μ`
  obtain ⟨hX, hmap⟩ := h
  refine ⟨hX, ?_⟩
  -- change of variables: `∫ ω, X ω ∂Ω.μ = ∫ y, y ∂unif01_sem`
  have hcv : ∫ ω, X ω ∂Ω.μ = ∫ y : ℝ, y ∂unif01_sem := by
    rw [hmap]
    exact (integral_map hX.aemeasurable aestronglyMeasurable_id).symm
  -- the mean of the uniform measure on `[0,1]` is `1/2`
  have e1 : ∫ y : ℝ, y ∂unif01_sem
      = ∫ a : ↥(Set.Icc (0 : ℝ) 1), (a : ℝ) ∂volume := by
    change ∫ y : ℝ, y ∂(Measure.map Subtype.val (volume : Measure ↥(Set.Icc (0 : ℝ) 1))) = _
    exact integral_map measurable_subtype_coe.aemeasurable aestronglyMeasurable_id
  have e2 : ∫ a : ↥(Set.Icc (0 : ℝ) 1), (a : ℝ) ∂volume
      = ∫ x in Set.Icc (0 : ℝ) 1, x ∂volume :=
    integral_subtype_comap measurableSet_Icc (fun x => x)
  have e3 : ∫ x in Set.Icc (0 : ℝ) 1, x ∂volume = 0.5 := by
    rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
    norm_num
  rw [hcv, e1, e2]; exact e3
