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
import Bppl.Lilac.BI
import Bppl.Lilac.Appl

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Almost Surely EQual-/
namespace Aseq
open MeasurableSpace Iris.BI.BIBase LProp Iris.BI Appl List Appl

variable {ds rs : List Ty} {A : Ty}

namespace helper
-- move to a measure theory helper file
open MeasureTheory in
/-- An equivalent way of stating the measurability condition of `≗`.  We require `MeasureableEq`
spaces just to satisfy this lemma, which is then required to prove transitivity of `≗`.
Appendix B.12 from Lilac paper
Make the `MeasurableSpace` parameters explicit since `msα` needs to be explicit.
This is because `α=HC` in our use case and we generally have two
measurable spaces 1) given by the probability space and 2) the finest one, `MeasurableSpace.pi`.
Here `msα` is option 1). And option 2) would be used in `X₁` and `X₂`, but we don't require
the measurability of these two maps so we just recieve the underlying parameters as functions here
(hence no mention of option 2). -/
lemma aseq_measurable_alt {α β : Type*} (msα : MeasurableSpace α) (msβ : MeasurableSpace β)
      (meβ : MeasurableEq β) {F : Set α} (hF : MeasurableSet F) (X₁ X₂ : α → β)
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

/-- Appendix B.13 from Lilac paper -/
lemma refl (E₁ : RV ⟪A⟫) : iprop( ⊢ E₁ ≗ E₁) := by
  rintro ⟨⟨ℱ, μ⟩, is_prob⟩ _
  simp [eq]
/-- Appendix B.13 from Lilac paper -/
lemma symm (E₁ E₂ : RV ⟪A⟫) : iprop(E₁ ≗ E₂ ⊢ E₂ ≗ E₁) := by
  rintro ⟨⟨ℱ, μ⟩, is_prob⟩ eq_l
  dsimp [eq] at ⊢ eq_l
  obtain ⟨h₁, h₂, h_meas_union⟩ := eq_l
  have symm_full_set : {ω | E₁ ω = E₂ ω} = {ω | E₂ ω = E₁ ω} :=
      by ext; exact ⟨Eq.symm, Eq.symm⟩
  constructor
  · rwa [← symm_full_set]
  · constructor
    · rwa [← symm_full_set]
    · intro x hx
      have h_meas_union_swap := h_meas_union (Prod.swap ⁻¹' x) (measurableSet_swap_iff.2 hx)
      have h_prod_swap :
          (fun ω ↦ (E₁ ω, E₂ ω)) ⁻¹' (Prod.swap ⁻¹' x) = (fun ω ↦ (E₂ ω, E₁ ω)) ⁻¹' x
        := by ext; simp
      rw [h_prod_swap, symm_full_set] at h_meas_union_swap
      exact h_meas_union_swap

/-- Appendix B.13 from Lilac paper -/
lemma trans (E₁ E₂ E₃ : RV ⟪A⟫) : iprop(E₁ ≗ E₂ ∧ E₂ ≗ E₃ ⊢ E₁ ≗ E₃) := by
  rintro ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨⟨meas_F₁₂, full_F₁₂, hF₁₂⟩, ⟨meas_F₂₃, full_F₂₃, hF₂₃⟩⟩
  let F₁₃ := {ω | E₁ ω = E₃ ω}

  have meas_F₁₃ : MeasurableSet F₁₃ := by sorry
  have full_F₁₃ : μ F₁₃ = 1 := by sorry
  have hF₁₃ : ∀ (x : Set (⟪A⟫ × ⟪A⟫)), MeasurableSet x → MeasurableSet (F₁₃ ∪ ⟨E₁, E₃⟩ᶠ⁻¹' x) := by
    sorry
  exact ⟨meas_F₁₃, full_F₁₃, hF₁₃⟩

-- Appendix B.15 from Lilac paper
lemma and_aseq_iff_sep_aseq (P : LProp) (E₁ E₂ : RV ⟪A⟫) :
    iprop(P ∧ (E₁ ≗ E₂) ⊣⊢ P ∗ (E₁ ≗ E₂)) :=
  sorry

-- Maybe the definition of persistently could be changed inspired by the requirements of
-- this proof obligation
/-- Appendix B.16 from Lilac paper -/
instance aseq_persisitent (E₁ E₂ : RV ⟪A⟫) : Persistent iprop(E₁ ≗ E₂) where
  persistent := sorry

/-- Appendix B.17 from Lilac paper -/
lemma transfer_own (E₁ E₂ : RV ⟪A⟫) : iprop(own E₁ ∧ E₁ ≗ E₂ ⊢ own E₂) := by
  rintro ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_own, h_eq⟩
  dsimp [own] at h_own ⊢
  dsimp [eq] at h_eq
  obtain ⟨h_meas_F, _, h_prod⟩ := h_eq
  let F := {ω | E₁ ω = E₂ ω}
  intro S hS
  -- Step 1: F ∪ X₂⁻¹' S is measurable
  have h1 : MeasurableSet (F ∪ E₂ ⁻¹' S) := by
    have := h_prod (Set.univ ×ˢ S) (MeasurableSet.univ.prod hS)
    convert this using 1
    ext ω; simp [Set.mem_preimage, Set.mem_prod, F]
  -- Step 2: Fᶜ ∩ X₂⁻¹' S is measurable
  have h2 : MeasurableSet (Fᶜ ∩ E₂ ⁻¹' S) := by
    have : Fᶜ ∩ E₂ ⁻¹' S = (F ∪ E₂ ⁻¹' S) \ F := by
      ext ω; simp [Set.mem_diff, Set.mem_compl_iff, Set.mem_inter_iff]; tauto
    rw [this]; exact h1.diff h_meas_F
  -- Step 3: F ∩ X₂⁻¹' S = F ∩ X₁⁻¹' S is measurable
  have h3 : MeasurableSet (F ∩ E₂ ⁻¹' S) := by
    have hFeq : F ∩ E₂ ⁻¹' S = F ∩ E₁ ⁻¹' S := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, F]
      constructor
      · rintro ⟨heq, hmem⟩; exact ⟨heq, heq ▸ hmem⟩
      · rintro ⟨heq, hmem⟩; exact ⟨heq, heq.symm ▸ hmem⟩
    rw [hFeq]; exact h_meas_F.inter (h_own hS)
  -- Step 4: X₂⁻¹' S = (F ∩ X₂⁻¹' S) ∪ (Fᶜ ∩ X₂⁻¹' S)
  have h4 : E₂ ⁻¹' S = (F ∩ E₂ ⁻¹' S) ∪ (Fᶜ ∩ E₂ ⁻¹' S) := by
    ext ω; simp [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  rw [h4]; exact h3.union h2

/-- Appendix B.17 from Lilac paper -/
lemma transfer_dist (E₁ E₂ : RV ⟪A⟫) (ν : MeasureTheory.Measure ⟪A⟫) :
    iprop(E₁ ∼ ν ∧ E₁ ≗ E₂ ⊢ E₂ ∼ ν) := by
  rintro ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_dist, h_aseq⟩
  dsimp [LProp.dist] at h_dist ⊢
  dsimp [LProp.eq] at h_aseq
  obtain ⟨h_meas_X₁, h_eq_dist⟩ := h_dist
  obtain ⟨h_meas_F, h_full_F, h_prod⟩ := h_aseq
  constructor
  · -- Measurability of X₂: same proof as transfer_own
    exact (transfer_own E₁ E₂ ⟨⟨ℱ, μ⟩, is_prob⟩ ⟨h_meas_X₁, h_meas_F, h_full_F, h_prod⟩ : (own E₂).1 ⟨⟨ℱ, μ⟩, is_prob⟩)
  · -- Distribution equality: since X₁ = X₂ a.e., Measure.bind μ (dirac ∘ X₁) = Measure.bind μ (dirac ∘ X₂)
    rw [h_eq_dist]
    -- bind μ f = (map f μ).join, so it suffices to show map f₁ = map f₂
    simp only [MeasureTheory.Measure.bind]
    congr 1
    apply MeasureTheory.Measure.map_congr
    -- Need: (fun ω ↦ dirac (X₁ ω)) =ᵐ[μ] (fun ω ↦ dirac (X₂ ω))
    -- Use Filter.EventuallyEq and show the set where they differ has measure 0
    have h_ae : ∀ᵐ ω ∂μ, E₁ ω = E₂ ω := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null
      · intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; exact hω
      · -- {ω | (E₁ γ)(D ω) ≠ (E₂ γ)(D ω)} has measure 0
        -- since its complement is F with μ F = 1
        convert MeasureTheory.measure_compl h_meas_F _ using 1 <;> aesop
    filter_upwards [h_ae] with ω hω
    rw [hω]

-- def subst (E : ValRand ds rs ⟪A⟫) (γ : TProd (⟪·⟫) ds)
--     : TProd (⟪·⟫) (A :: rs) -m→ TProd (⟪·⟫) (A :: rs) :=
--   ⟨fun r_env ↦ (E γ r_env, r_env), Measurable.prod (E γ).2 (measurable_id)⟩
--   ∘ₘ ⟨Prod.snd, measurable_snd⟩

-- def subst' {A : Ty} (E : ValRand ds rs ⟪A⟫) (γ : TProd (⟪·⟫) ds)
--     : TProd (⟪·⟫) (rs) -m→ TProd (⟪·⟫) (A :: rs) :=
--   ⟨fun r_env ↦ (E γ r_env, r_env), Measurable.prod (E γ).2 (measurable_id)⟩

-- abbrev measurableProd [MeasurableSpace β] [MeasurableSpace γ₁] [MeasurableSpace γ₂]
--     (f : β -m→ γ₁) (g : β -m→ γ₂) : β -m→ γ₁ × γ₂ :=
--   ⟨fun r ↦ (f r, g r), Measurable.prod f.2 g.2⟩

-- notation " ⟨ " f " , " g " ⟩ᵐ " => measurableProd f g

abbrev randValProd [MeasurableSpace β] [MeasurableSpace γ₁] [MeasurableSpace γ₂]
    (f : α → β -m→ γ₁) (g : α → β -m→ γ₂) : α → β -m→ γ₁ × γ₂ :=
  fun d ↦ ⟨fun r ↦ (f d r, g d r), Measurable.prod (f d).2 (g d).2⟩

notation " ⟨ " f " , " g " ⟩ʳ " => randValProd f g

-- instance {α : Type*} [MeasurableSpace α] {r : Ty} : Coe (ValRand ds rs α) (ValRand ds (r :: rs) α) where
--   coe E := fun ds ↦ E ds ∘ₘ ⟨Prod.snd, measurable_snd⟩

-- abbrev drop {r : Ty} (E : ValRand ds rs ⟪A⟫) : ValRand ds (r :: rs) ⟪A⟫ :=
--   fun ds ↦ E ds ∘ₘ ⟨Prod.snd, measurable_snd⟩

-- /-- E substitutes the rv at the head of the randEnv list (generally denoted as `D`) -/
-- notation F "[ " E " /_] " => substValRand id (subst E) F

-- /-- Appendix B.17 from Lilac paper
-- clarification: `own(F[E₁], F[E₂])` refers to owning the rv which takes an input and applies it to
-- both the function `F[E₁]` and `F[E₂]`. -/
-- lemma congruence {B : Ty} (F : ValRand ds (A :: rs) ⟪B⟫) (E₁ E₂ : ValRand ds rs ⟪A⟫) :
--     iprop(own ⟨F[E₁/_], F[E₂/_]⟩ʳ ∧ drop E₁ ≗ drop E₂ ⊢ F[E₁/_] ≗ F[E₂/_]) := by
--   rintro ⟨γ, XD⟩ ⟨Ω, is_prob⟩ ⟨h_own, ⟨meas_E₁₂, full_E₁₂, hE₁₂⟩⟩
--   let E₁₂ := {ω | (↑(drop E₁ γ) ∘ ↑XD) ω = (↑(drop E₂ γ) ∘ ↑XD) ω}
--   let X₁ : RV ⟪A⟫ := (drop E₁) γ ∘ₘ XD
--   let X₂ : RV ⟪A⟫ := (drop E₂) γ ∘ₘ XD
--   have alt_hE₁₂ := (helper.aseq_measurable_alt Ω.ms ⟪A⟫ᵐ ⟪A⟫ᵐᵉ meas_E₁₂ X₁ X₂).out 0 1
--   apply alt_hE₁₂.1 at hE₁₂
--   let X₂D : EnvRand (A :: rs):= (subst E₂ γ) ∘ₘ XD
--   let X₁D : EnvRand (A :: rs):= (subst E₁ γ) ∘ₘ XD
--   let F₁ := (F[E₁/_]) γ ∘ₘ XD
--   let F₂ := (F[E₂/_]) γ ∘ₘ XD
--   -- The simplified version by applying `substValRand` def and reducing
--   have subst_lemma₁ : F₁ = F γ ∘ₘ X₁D := rfl
--   have subst_lemma₂ : F₂ = F γ ∘ₘ X₂D := rfl
--   let F₁₂ := {ω | F₁ ω = F₂ ω}
--   dsimp [own] at h_own
--   have meas_F₁₂ : @MeasurableSet _ Ω.ms F₁₂ := by
--     have hdiag : F₁₂ = ⟨F₁, F₂⟩ᶠ⁻¹' (Set.diagonal ⟪B⟫) := by
--       ext ω
--       simp only [Set.mem_preimage, Set.mem_diagonal_iff, fProd]
--       rfl
--     rw [hdiag]
--     exact h_own (@measurableSet_diagonal _ ⟪B⟫ᵐ ⟪B⟫ᵐᵉ)
--   have full_F₁₂ : Ω.μ F₁₂ = 1 := by
--     -- E₁₂ ⊆ F₁₂: if E₁ and E₂ agree on ω, then F applied to both also agrees
--     have h_sub : E₁₂ ⊆ F₁₂ := by
--       intro ω hω
--       have : (subst E₁ γ).1 (XD.1 ω) = (subst E₂ γ).1 (XD.1 ω) := by
--         dsimp [subst, MeasurableFunc.comp]
--         exact congr_arg₂ Prod.mk hω rfl
--       exact congrArg (F γ).1 this
--     exact le_antisymm (MeasureTheory.prob_le_one)
--       (full_E₁₂ ▸ MeasureTheory.measure_mono h_sub)
--   -- F₁₂ contains the entire pullback σ-algebra (F₁, F₂)⁻¹ (B ⊗ B), and so contains F₁₂ ∪
--   -- (F₁, F₂)⁻¹ (B ⊗ B) too.
--   have hF₁₂ : ∀ (x : Set (⟪B⟫ × ⟪B⟫)), MeasurableSet x →
--       @MeasurableSet _ Ω.ms (F₁₂ ∪ ⟨F₁, F₂⟩ᶠ⁻¹' x) := by
--     intro x hx
--     exact meas_F₁₂.union (h_own hx)
--   exact ⟨meas_F₁₂, full_F₁₂, hF₁₂⟩

-- B.19, don't think this is needed

end Aseq
namespace WP
open ProbabilityTheory Appl PMF NNReal List
open Iris.BI.BIBase LProp Iris.BI Appl List Appl
-- importing all of MeasureTheory imports an operator ∗ conflicting with the separating conjunct
open MeasureTheory (Measure)
variable {ds : List Ty} {rs : List Ty} {r r' : Ty} {A B ty₁ ty₂ : Ty}
noncomputable section

-- /-- used in statement of `wp_frame` -/
-- instance : Coe (LProp ds rs) (LProp ds (r :: rs)) where
--   coe P := ⟨fun (γ, D) Ω ↦ P.1 (γ, ⟨Prod.snd, measurable_snd⟩ ∘ₘ D) Ω, sorry⟩

-- abbrev drop (P : LProp ds rs) : LProp ds (r :: rs) :=
--   -- trivial sorry. show monotonicity by extra variable unused.
--   ⟨fun (γ, D) Ω ↦ P.1 (γ, ⟨Prod.snd, measurable_snd⟩ ∘ₘ D) Ω, sorry⟩

-- variable {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} in
-- lemma measurable_dropSnd : Measurable (fun (x, _y, z) => (x,z) : α × (β × γ) → α × γ) :=
--   by measurability
--   -- Measurable.prod measurable_fst (measurable_snd.comp measurable.snd)

-- /-- Used in `wp_bind`. Required since the nesting of `wp`s adds variables to the head of the rand
-- env.  So if we want to ignore the topmost variable in a do block, that actually requires ignoring
-- an inner variable in the randenv list. -/
-- abbrev dropSnd (P : LProp ds (r :: rs)) : LProp ds (r :: r' :: rs) :=
--   -- show monotonicity by extra variable unused. aesop? works but needs golfing
--   ⟨fun (γ, D) Ω ↦ P.1 (γ, ⟨_, measurable_dropSnd⟩ ∘ₘ D) Ω, sorry⟩

-- /-- A bulding block for subst which "cons"es on the rv obtained from the program `ret M`. -/
-- def subst' (M : TProd (⟪·⟫) (rs) -m→ ⟪A⟫)
--     : TProd (⟪·⟫) (rs) -m→ TProd (⟪·⟫) (A :: rs) :=
--   ⟨fun r_env ↦ (M r_env, r_env), Measurable.prod M.2 (measurable_id)⟩

-- -- def subst'' (M : Term rs A) : TProd (⟪·⟫) (A :: rs) -m→ TProd (⟪·⟫) (A :: rs)
-- --   := (subst' M.den) ∘ₘ ⟨Prod.snd, measurable_snd⟩

-- def subst (P : LProp ds (A::rs)) (M : Term rs A)
--     : LProp ds (rs) :=
--   ⟨fun (γ, D) Ω ↦ P.1 (γ, (subst' M.den) ∘ₘ D) Ω, sorry⟩

-- /-- M substitutes the rv at the head of the randEnv list (generally denoted as `D`).
-- used in the rule `wp_ret`. -/
-- notation Q "[ " M " /_] " => subst Q M

-- Appendix B.20
-- it is unclear how to write down Q_of_P? Is it better to use -∗ ?
lemma wp_cons {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)}
    (Q_of_P : ∀ X : RV ⟪A⟫, iprop(P X ⊢ Q X)) : iprop(wp M P ⊢ wp M Q) := by
  sorry

/-- Notice the requirement for a second `iprop` quotation. This is because of the devious
coercion of F which ignores the extra random variable introduced into the environment by `wp`.
Make the coercion explicit by using `drop` instead. -/
lemma wp_frame {F : LProp} {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)} :
    iprop(F ∗ (wp M Q) ⊢ wp M (λ X ↦ iprop(F ∗ Q X))) :=
  sorry

lemma wp_disj {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)} :
    iprop((wp M P) ∨ (wp M Q) ⊢ wp M (λ X ↦ iprop(P X ∨ Q X))) := sorry

-- Appendix B.22 from Lilac paper
-- TODO: It is unclear how to express the substitution of `wp_ret`. Just a function?

lemma wp_ret (Q : RV ⟪A⟫ → LProp) (D : RV (TProd (⟪·⟫) rs)) (M : Term rs A) :
    iprop((Q (M.den ∘ₚ D)) ⊢ wp ((Term.ret M).den ∘ₚ D) Q) := by
  sorry

lemma wp_bind (Q : RV ⟪B⟫ → LProp) (D : RV (TProd (⟪·⟫) rs))
      (M : Term rs A.G) (N : Term (A::rs) B.G) :
    wp (M.den ∘ₚ D) (λ X ↦ (wp (N.den ∘ₚ (X ; D)) Q)) ⊢ wp ((M.bind N).den ∘ₚ D) Q :=
  sorry

/-- The semantic (native lean) uniform distribution in the interval [0,1]. -/
def unif01_sem : Measure ⟪Ty.real⟫ := uniformOn (Set.Icc 0 1)

def ber_sem (p : ℝ≥0) (hp : p ≤ 1) : TProd (⟪·⟫) ds → Measure Bool :=
  fun _ ↦ (bernoulli p hp).toMeasure

-- /-- Variable at the head of the random environment list. -/
-- def fst_rand : ValRand ds (A::rs) ⟪A⟫ :=
--   fun _d_env ↦ ⟨fun r_env ↦ r_env.get .head , List.TProd.measurable_get .head⟩

-- D is a dummy and is only used to impart an unused context to Term.unif01
-- Need to make sure this boilerplate doesn't bother the user
-- TODO `⟪Ty.real⟫` not definitionally equal to `ℝ` because `Ty.den : MeasCat`
lemma wp_unif (Q : RV ⟪Ty.real⟫ → LProp) (D : RV (TProd (⟪·⟫) rs)) :
    iprop(
      ∀ (X : RV ⟪Ty.real⟫), iprop(X ∼ unif01_sem -∗ Q X))
     ⊢ wp ((@Term.unif01 rs).den ∘ₚ D) Q :=
  sorry

-- lemma wp_flip (p : ℝ≥0) (hp : p ≤ 1) (Q : LProp ds (Ty.bool :: rs)) :
--     forall_rv Ty.bool iprop(fst_rand ∼ (ber_sem p hp) -∗ Q) ⊢ wp ⦃Term.flip p hp⦄ Q :=
--   sorry

-- lemma wp_let (M : Term rs (.G ty₁)) (N : Term (ty₁ :: rs) (.G ty₂))
-- Term ctx (.G ty₁) → Term (ty₁ :: ctx) (.G ty₂) → Term ctx (.G ty₂)

end
end WP
