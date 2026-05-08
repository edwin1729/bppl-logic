/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Mathlib

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
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, _⟩ _
  simp [eq]
/-- Appendix B.13 from Lilac paper -/
lemma symm (E₁ E₂ : RV ⟪A⟫) : iprop(E₁ ≗ E₂ ⊢ E₂ ≗ E₁) := by
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, _⟩ eq_l
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
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, _⟩ ⟨⟨meas_F₁₂, full_F₁₂, hF₁₂⟩, ⟨meas_F₂₃, full_F₂₃, hF₂₃⟩⟩
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
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, _⟩ ⟨h_own, h_eq⟩
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
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, ff⟩ ⟨h_dist, h_aseq⟩
  dsimp [LProp.dist] at h_dist ⊢
  dsimp [LProp.eq] at h_aseq
  obtain ⟨h_meas_X₁, h_eq_dist⟩ := h_dist
  obtain ⟨h_meas_F, h_full_F, h_prod⟩ := h_aseq
  constructor
  · -- Measurability of X₂: same proof as transfer_own
    exact (transfer_own E₁ E₂ ⟨⟨⟨ℱ, μ⟩, is_prob⟩, ff⟩ ⟨h_meas_X₁, h_meas_F, h_full_F, h_prod⟩ :
      (own E₂).1 ⟨⟨⟨ℱ, μ⟩, is_prob⟩, _⟩)
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

/-- Appendix B.17 from Lilac paper
clarification: `own(F[E₁], F[E₂])` refers to owning the rv which takes an input and applies it to
both the function `F[E₁]` and `F[E₂]`. -/
lemma congruence {B : Ty} (F : RV ⟪A⟫ → RV ⟪B⟫) (E₁ E₂ : RV ⟪A⟫) :
    iprop(own ⟨F E₁, F E₂⟩ʳ ∧ E₁ ≗ E₂ ⊢ F E₁ ≗ F E₂) := by

  rintro Ω ⟨h_own, ⟨meas_E₁₂, full_E₁₂, hE₁₂⟩⟩

  let E₁₂ := {ω | E₁ ω = E₂ ω}
  have alt_hE₁₂ := (helper.aseq_measurable_alt Ω.ms ⟪A⟫ᵐ ⟪A⟫ᵐᵉ meas_E₁₂ E₁ E₂).out 0 1
  apply alt_hE₁₂.1 at hE₁₂
  let F₁₂ := {ω | F E₁ ω = F E₂ ω}
  dsimp [own] at h_own
  have meas_F₁₂ : @MeasurableSet _ Ω.ms F₁₂ := by
    have hdiag : F₁₂ = ⟨F E₁, F E₂⟩ᶠ⁻¹' (Set.diagonal ⟪B⟫) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_diagonal_iff, fProd]
      rfl
    rw [hdiag]
    exact h_own (@measurableSet_diagonal _ ⟪B⟫ᵐ ⟪B⟫ᵐᵉ)
  have full_F₁₂ : Ω.μ F₁₂ = 1 := by
    -- E₁₂ ⊆ F₁₂: if E₁ and E₂ agree on ω, then F applied to both also agrees
    have h_sub : E₁₂ ⊆ F₁₂ := by

      intro ω hω
      change E₁ ω = E₂ ω at hω
      change F E₁ ω = F E₂ ω

      -- have : (subst E₁ γ).1 (XD.1 ω) = (subst E₂ γ).1 (XD.1 ω) := by
      --   dsimp [subst, MeasurableFunc.comp]
      --   exact congr_arg₂ Prod.mk hω rfl
      sorry
      -- exact congrArg F (by
      --   -- simp at hω
      --   exact hω)
    sorry
    -- exact le_antisymm (MeasureTheory.prob_le_one)
      -- (full_E₁₂ ▸ MeasureTheory.measure_mono h_sub)
  -- F₁₂ contains the entire pullback σ-algebra (F₁, F₂)⁻¹ (B ⊗ B), and so contains F₁₂ ∪
  -- (F₁, F₂)⁻¹ (B ⊗ B) too.
  have hF₁₂ : ∀ (x : Set (⟪B⟫ × ⟪B⟫)), MeasurableSet x →
      @MeasurableSet _ Ω.ms (F₁₂ ∪ ⟨F E₁, F E₂⟩ᶠ⁻¹' x) := by
    intro x hx
    exact meas_F₁₂.union (h_own hx)
  exact ⟨meas_F₁₂, full_F₁₂, hF₁₂⟩

-- B.19, don't think this is needed

end Aseq
namespace WP
open ProbabilityTheory Appl PMF NNReal List
open Iris.BI.BIBase LProp Iris.BI Appl List Appl
-- importing all of MeasureTheory imports an operator ∗ conflicting with the separating conjunct
open MeasureTheory (Measure)
variable {ds : List Ty} {rs : List Ty} {r r' : Ty} {A B ty₁ ty₂ : Ty}
noncomputable section

-- Appendix B.20
-- it is unclear how to write down Q_of_P? Is it better to use -∗ ?
lemma wp_cons {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)}
    (Q_of_P : ∀ X : RV ⟪A⟫, iprop(P X ⊢ Q X)) : iprop(wp M P ⊢ wp M Q) := by
  intro Ω wp_l Ω_fr μ hΩ
  sorry

lemma wp_frame {F : LProp} {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)} :
    iprop(F ∗ (wp M Q) ⊢ wp M (fun X ↦ iprop(F ∗ Q X))) := by
  rintro Ω ⟨Ω_F, Ω_M, hΩ_F_M, _,  hF, h_M⟩ Ω_fr μ hΩ
  -- Proof sketch:
  -- 1. Using `le_mul_mono` establish `Ω_fr ⋆ (Ω_F ⋆ Ω_M)` exists
  --    from `Ω_fr ⋆ Ω ≤ .mk μ` and `(Ω_F ⋆ Ω_M) ≤ Ω`
  -- 2. Using `assoc` (specifically the helper `exists_left`) establish `(Ω_fr ∗ Ω_F)` exists
  -- 3. Feed `(Ω_fr ∗ Ω_F)` as the Ω_fr for `h_M`. Next supply proof using `assoc`
  --    that `Ω_fr ∗ (Ω_F ∗ Ω_M)`.
  -- 4. By applying the h_M above we easily reach our goal as required. We now get the
  --    `X : RV _` and an `Ω'` and `μ'` such that the `measure bind` based thing in the
  --    `wp` def and the post condition hold.
  --    The measure bind thing is the same on both sides. On the left hand side wp we just
  --    additionally need to show that for all X, F also holds.
  sorry

lemma wp_disj {P Q : RV ⟪A⟫ → LProp} {M : RV (Measure ⟪A⟫)} :
    iprop((wp M P) ∨ (wp M Q) ⊢ wp M (fun X ↦ iprop(P X ∨ Q X))) := sorry

-- Appendix B.22 from Lilac paper
-- TODO: It is unclear how to express the substitution of `wp_ret`. Just a function?

lemma wp_ret (Q : RV ⟪A⟫ → LProp) (D : RV (TProd (⟪·⟫) rs)) (M : Term rs A) :
    iprop((Q (M.den ∘ₚ D)) ⊢ wp ((Term.ret M).den ∘ₚ D) Q) := by
  sorry

lemma wp_bind (Q : RV ⟪B⟫ → LProp) (D : RV (TProd (⟪·⟫) rs))
      (M : Term rs A.G) (N : Term (A::rs) B.G) :
    wp (M.den ∘ₚ D) (fun X ↦ (wp (N.den ∘ₚ (X ; D)) Q)) ⊢ wp ((M.bind N).den ∘ₚ D) Q :=
  sorry

/-- The semantic (native lean) uniform distribution in the interval [0,1]. -/
def unif01_sem : Measure ⟪Ty.real⟫ := uniformOn (Set.Icc 0 1)

def ber_sem (p : ℝ≥0) (hp : p ≤ 1) : TProd (⟪·⟫) ds → Measure Bool :=
  fun _ ↦ (bernoulli p hp).toMeasure


lemma wp_meas {A : Ty} (Q : RV ⟪A⟫ → LProp) (μ : Measure ⟪A⟫) :
    iprop(∀ (X : RV ⟪A⟫), iprop(X ∼ μ -∗ Q X))
    ⊢ wp ⟨fun _ ↦ μ, measurable_const⟩ Q := by
  rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, n, ff⟩ lhs Ω_fr Ω_pre μ hΩ_pre
  -- let X : RV ⟪A⟫ := ⟨fun ω ↦ ω n, sorry⟩
  sorry


open unitInterval

/-! ### Infrastructure for wp_unif (B.21) -/

open MeasureTheory in

/-- If `a ⋆ b = b ⋆ a` (from `Pcm.comm`), then `Option.get` yields equal values. -/
lemma PSp.get_comm (a b : PSp) (hab : ✓'(a ⋆ b)) (hba : ✓'(b ⋆ a)) :
    ↓hab = ↓hba := by
  have h : a ⋆ b = b ⋆ a := Pcm.comm a b
  set x := (a ⋆ b).get hab
  set y := (b ⋆ a).get hba
  have hax : a ⋆ b = some x := Option.some_get hab ▸ rfl
  have hay : b ⋆ a = some y := Option.some_get hba ▸ rfl
  exact Option.some_injective _ (hax.symm.trans (h.trans hay))

-- Appendix B.21 from Lilac paper — "Uniform" proof rule.
--
-- Given the precondition ∀ X, (X ∼ unif01 -∗ Q X), the weakest precondition for sampling
-- from the uniform distribution on [0, 1] entails Q for some fresh random variable X.
--
-- Informal proof (B.21):
-- Since the combined resource (Ω_fr ⋆ Ω) has finite footprint k, the σ-algebra depends
-- only on the first k coordinates of the Hilbert cube HC. We pick the fresh random
-- variable X(ω) = ↑(ω k) (the (k+1)-th coordinate, which is independent of everything
-- seen so far). We define Ω_k as the probability space whose σ-algebra is generated by
-- coordinate k alone (coordMS k), equipped with the Lebesgue measure on that coordinate.
-- Since Ω and Ω_k have disjoint footprints (Ω uses coords < k, Ω_k uses coord k),
-- their independent product Ω ⋆ Ω_k exists. By associativity, the frame
-- Ω_fr ⋆ (Ω ⋆ Ω_k) also exists.
--
-- The new measure μ' is the product of the marginal of μ on the first k coords
-- with the infinite product of uniform distributions on the remaining coords.
-- Under μ', coord k is uniform ⟹ X ~ unif01_sem, so the wand gives Q X.

open MeasureTheory in
def PSpace.mk'' {Ω : Type*} {ms ms' : MeasurableSpace Ω} (μ : @ProbabilityMeasure Ω ms)
    (ms'_le_ms : ms' ≤ ms) : PSpace Ω :=
  ⟨⟨ms' , μ.1.trim ms'_le_ms⟩, sorry ⟩

/-- `MeasurableSpace.sum` (from MeasureOnSpace.lean) equals `⊔` (the lattice sup). -/
private lemma sum_eq_sup {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    MeasurableSpace.sum m₁ m₂ = m₁ ⊔ m₂ := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s (h | h)
    · exact @le_sup_left _ _ m₁ m₂ s h
    · exact @le_sup_right _ _ m₁ m₂ s h
  · apply sup_le <;> intro s hs <;>
    exact MeasurableSpace.measurableSet_generateFrom
      (by first | left; exact hs | right; exact hs)

-- Appendix B.21 from Lilac paper — "Uniform" proof rule.
open HC in
open MeasureTheory in
lemma wp_unif (Q : RV ⟪Ty.real⟫ → LProp) (D : RV (TProd (⟪·⟫) rs)) :
    iprop(∀ (X : RV ⟪Ty.real⟫), iprop(X ∼ unif01_sem -∗ Q X))
    ⊢ wp ((@Term.unif01 rs).den ∘ₚ D) Q := by
  rintro Ω lhs Ω_fr Ω_pre μ hΩ_pre
  -- Extract the finite footprint: n is the number of coordinates used
  obtain ⟨n, ff_pre⟩ := (↓Ω_pre).finite_footprint
  -- Ω.ms ≤ ↓Ω_pre.ms (since Ω is a component of the independent product)
  have hΩ_le_pre : Ω.ms ≤ (↓Ω_pre).ms := by
    set x := (Ω_fr ⋆ Ω).get Ω_pre
    have hsome : Ω_fr ⋆ Ω = some x := (Option.some_get Ω_pre).symm ▸ rfl
    have hval : Ω_fr.1 ⋆ Ω.1 = some x.1 := by
      have := PSp.psp_val_binop Ω_fr Ω
      rw [hsome] at this; simpa using this.symm
    exact (PSpace.le_of_isIndependentProduct_right
      (PSpace.isIndependentProduct_of_binop_eq_some hval)).1
  let X : RV ⟪Ty.real⟫ := ⟨fun ω ↦ ω n, by fun_prop⟩
  -- Step 2: Constructions that need default MeasurableSpace (before ms_k shadows it)
  let leb : @ProbabilityMeasure HC Inf_borel :=
    ⟨Measure.infinitePiNat (fun _ => (volume : Measure I)), inferInstance⟩
  let μ_k : ProbabilityMeasure (Fin n → I) :=
    μ.map (measurable_fst.comp (HC.splitBi n).measurable).aemeasurable
  let μ' : @ProbabilityMeasure HC Inf_borel :=
    (μ_k.prod leb).map (HC.splitBi n).symm.measurable.aemeasurable
  let Ω_n : PSp := ⟨PSpace.mk'' leb (N_nil_I_borel_le_Inf_borel n), ff_N_nil_I_borel⟩
  -- Now extract ms_pre (after μ_k/μ' definitions to avoid instance shadowing)
  obtain ⟨ms_pre, h_ms_pre⟩ := ff_pre

  -- σ-algebra equality: the sum of the two sub-σ-algebras equals the combined one
  -- Uses: .sum = ⊔ (sum_eq_sup), commutativity of ⊔, and commute_over_equiv4
  have h_sum_eq : (↓Ω_pre).1.ms.sum Ω_n.1.ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil):= by
    show (↓Ω_pre).ms.sum Ω_n.ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)
    rw [h_ms_pre, sum_eq_sup, sup_comm]
    exact commute_over_equiv4 ms_pre
  -- Construct the PSpace witness for the independent product
  let r_pspace : PSpace HC :=
    PSpace.mk'' μ' (unSplitTri_I_borel_le_Inf_borel ms_pre)
  -- r_pspace.ms equals the required sum (by construction and h_sum_eq)
  have h_r_ms : r_pspace.ms = (↓Ω_pre).1.ms.sum Ω_n.1.ms :=
    h_sum_eq.symm
  -- The measure product condition: under μ', sets from disjoint coordinates
  -- factor as a product. This is the key measure-theoretic fact:
  -- μ' = (μ_k × leb) ∘ (splitBi n)⁻¹ is a product measure, and sets measurable
  -- wrt ↓Ω_pre (first n coords) are independent from sets measurable wrt Ω_n (coord n).
  have h_measure_product :
      ∀ E (_ : MeasurableSet[(↓Ω_pre).1.ms] E)
        F (_ : MeasurableSet[Ω_n.1.ms] F),
        r_pspace.μ (E ∩ F) = (↓Ω_pre).1.μ E * Ω_n.1.μ F := by
    sorry
  -- Assemble the independent product proof
  have h_indep : r_pspace =ᵢ (↓Ω_pre).1 ⊕ᵢ Ω_n.1 :=
    ⟨h_r_ms, h_measure_product⟩
  -- Show the PSp PCM operation is defined (∃! r, r =ᵢ p ⊕ᵢ q)
  -- We use PSpace.binop_eq_some_of_isIndependentProduct at the PSpace level,
  -- then lift to PSp via psp_val_binop.
  have h_pspace_binop : (↓Ω_pre).1 ⋆ Ω_n.1 = some r_pspace :=
    PSpace.binop_eq_some_of_isIndependentProduct h_indep
  have Ω_post : ✓'(↓Ω_pre ⋆ Ω_n) := by
    have h_map := PSp.psp_val_binop (↓Ω_pre) Ω_n
    rw [h_pspace_binop] at h_map
    cases h : (↓Ω_pre) ⋆ Ω_n with
    | some _ => rfl
    | none => simp [h] at h_map
  have eq_Ω_post_ms : (↓Ω_post).ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil) := sorry
  have Ω' : ✓'(Ω ⋆ Ω_n) := by sorry -- from assoc of PSp applied on Ω_post
  have Ω_post_alt : ✓'(Ω_fr ⋆ ↓Ω') := by sorry -- from assoc of PSp applied on Ω_post
  have eq_Ω_post : ↓Ω_post = ↓Ω_post_alt := by sorry
  use X, ↓Ω', Ω_post_alt, μ'

  refine ⟨?Ω_post_le, ?bind_eq, ?postcond⟩
  case Ω_post_le =>
    rw [← eq_Ω_post]

    constructor
    · change (↓Ω_post).ms ≤ Inf_borel
      sorry
    ·
      -- dsimp
      -- subst eq_Ω_post_ms

      rw [@Measure.ext_iff _ (↓Ω_post).ms (↓Ω_post).μ ((PSpace.mk' μ').μ.cast (↓Ω_post).ms)]
      apply MeasurableSpace.induction_on_inter
      · apply MeasureOnSpace.isPiSystem_generator (p := (↓Ω_pre).1.1) (q := Ω_n.1.1)
      · simp only [measure_empty, Measure.cast_eq_self]
      · intro t ht

        sorry
      ·
        sorry
      ·
        sorry
      ·
        sorry

    -- simp [PSp.toPSpace, PSpace.mk', Option.isSome_dite, LE.le]
    -- (↓hfr_Ω').1 ≤ PSpace.mk' μ': μ' agrees with Ω_fr⋆Ω on their coords
    -- and with Ω_k on coord k, by construction of μ' = μ_k ⊗ leb.
  case bind_eq =>
    -- change ((fun ω ↦ (fun v ↦ Measure.dirac v) ∘ₘ (Term.unif01.den ∘ₚ D) ω) ∘ₘ μ) = ((fun ω ↦ Measure.dirac (X ω)) ∘ₘ μ')
    -- change Measure.bind μ (fun ω ↦ Measure.bind ((Term.unif01.den ∘ₚ D) ω) (fun v ↦ Measure.dirac v)) =
    --   (Measure.bind μ' (fun ω ↦ Measure.dirac (X ω)))

    calc Measure.bind μ.1 (fun ω ↦ Measure.bind ((Term.unif01.den ∘ₚ D) ω) fun v ↦ Measure.dirac v)
        = Measure.bind μ.1 (fun ω ↦ Measure.bind unif01_sem (fun v ↦ Measure.dirac v)) := by

          sorry
      _ = Measure.bind unif01_sem (fun v ↦ Measure.dirac v) := sorry
      _ = (Measure.bind μ' (fun ω ↦ Measure.dirac (X ω))) := sorry

    -- change ((fun ω ↦ (fun v ↦ Measure.dirac v) ∘ₘ (Term.unif01.den ∘ₚ D) ω) ∘ₘ μ) = ((fun ω ↦ Measure.dirac (X ω)) ∘ₘ μ')

    --   (Measure.bind μ.1 (fun ω ↦ Measure.bind (M ω) (fun v ↦ Measure.dirac v))) =
    -- (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (X ω))) ∧

        -- sorry
  case postcond =>
    -- Q X via wand elimination
    dsimp only [BIBase.forall, BIBase.sForall] at lhs
    have h_wand := lhs iprop(X ∼ unif01_sem -∗ Q X) ⟨X, rfl⟩
    -- have X_meas : @Measurable HC ⟪Ty.real⟫ ms_pre _ X := HC.coordProj_measurable k
    have X_dist : unif01_sem = Measure.bind Ω_n.μ (fun ω ↦ Measure.dirac (X ω)) := by
      sorry
    --fill below sorry with X_meas
    have h_qx := h_wand Ω_n ((Pcm.comm Ω Ω_n) ▸ Ω') ⟨sorry, X_dist⟩
    suffices h : ↓((Pcm.comm Ω Ω_n) ▸ Ω') = ↓Ω' by exact h ▸ h_qx
    exact PSp.get_comm Ω_n Ω ((Pcm.comm Ω Ω_n) ▸ Ω') Ω'

end
end WP
