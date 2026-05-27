/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules.WPUnifHelpers


namespace WP
noncomputable section

open unitInterval ProbabilityTheory ProbabilityTheory.Kernel MeasureTheory MeasureTheory.Measure
open LProp Appl
open Iris.BI Krm HC

-- def ber_sem (p : ℝ≥0) (hp : p ≤ 1) : TProd (⟪·⟫) ds → Measure Bool :=
--   fun _ ↦ (bernoulli p hp).toMeasure

-- lemma wp_meas {A : Ty} (Q : RV ⟪A⟫ → LProp) (μ : Measure ⟪A⟫) :
--     iprop(∀ (X : RV ⟪A⟫), iprop(X ∼ μ -∗ Q X))
--     ⊢ wp ⟨fun _ ↦ μ, measurable_const⟩ Q := by
--   rintro ⟨⟨⟨ℱ, μ⟩, is_prob⟩, n, ff⟩ lhs Ω_fr Ω_pre μ hΩ_pre
--   -- let X : RV ⟪A⟫ := ⟨fun ω ↦ ω n, sorry⟩
--   sorry

def PSpace.mk'' {Ω : Type*} {ms ms' : MeasurableSpace Ω} (μ : @ProbabilityMeasure Ω ms)
    (ms'_le_ms : ms' ≤ ms) : PSpace Ω :=
  ⟨⟨ms', μ.1.trim ms'_le_ms⟩, sorry⟩

-- Appendix B.21 from Lilac paper — "Uniform" proof rule.
lemma wp_unif (Q : RV ⟪Ty.real⟫ → LProp) (D : RV (List.TProd (⟪·⟫) rs)) :
    iprop(∀ (X : RV ⟪Ty.real⟫), iprop(X ∼ unif01_sem -∗ Q X))
    ⊢ wp ((@Term.unif01 rs).den ∘ᵣ D) Q := by
  rintro Ω lhs Ω_fr Ω_pre μ hΩ_pre _ _ D_ext
  -- Extract the finite footprint: n is the max number of coordinates used among both
  -- the resource and (`Ω_pre`) and arbitrary `RV` (`D_ext`)
  obtain ⟨n₁, ff_pre⟩ := (↓Ω_pre).finite_footprint
  let n₂ := D_ext.n
  have ff_D_ext := D_ext.ff.choose_spec
  let n := max n₁ n₂
  have ff_pre := HC.finite_footprint_of_ge (le_max_left n₁ n₂) ff_pre
  have ff_D_ext := HC.finite_footprint_of_ge (le_max_right n₁ n₂) ff_D_ext
  -- Ω.ms ≤ ↓Ω_pre.ms (since Ω is a component of the independent product)
  have hΩ_le_pre : Ω.ms ≤ (↓Ω_pre).ms := by
    set x := (Ω_fr ⋆ Ω).get Ω_pre
    have hsome : Ω_fr ⋆ Ω = some x := (Option.some_get Ω_pre).symm ▸ rfl
    have hval : Ω_fr.1 ⋆ Ω.1 = some x.1 := by
      have := PSp.psp_val_binop Ω_fr Ω
      rw [hsome] at this; simpa using this.symm
    exact (PSpace.le_of_isIndependentProduct_right
      (PSpace.Krm.isIndependentProduct_of_binop_eq_some hval)).1
  let X : RV ⟪Ty.real⟫ := ⟨⟨fun ω ↦ ω n, by fun_prop⟩, sorry⟩
  -- Step 2: Constructions that need default MeasurableSpace (before ms_k shadows it)
  let μ_k : ProbabilityMeasure (Fin n → I) :=
    μ.map (measurable_fst.comp (HC.splitBi n).measurable).aemeasurable
  let μ' : @ProbabilityMeasure HC Inf_borel :=
    (μ_k.prod lebHC).map (HC.splitBi n).symm.measurable.aemeasurable
  -- could have equiavalently also used `leb` instead of `μ'`. This makes the proof easier though
  let Ω_n : PSp := ⟨PSpace.mk'' μ' (N_nil_I_borel_le_Inf_borel n), ff_N_nil_I_borel⟩
  -- Now extract ms_pre (after μ_k/μ' definitions to avoid instance shadowing)
  obtain ⟨ms_pre, h_ms_pre⟩ := ff_pre

  -- σ-algebra equality: the sum of the two sub-σ-algebras equals the combined one
  -- Uses: .sum = ⊔ (sum_eq_sup), commutativity of ⊔, and commute_with_add_dim
  have h_sum_eq : (↓Ω_pre).1.ms.sum Ω_n.1.ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil):= by
    show (↓Ω_pre).ms.sum Ω_n.ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)
    rw [h_ms_pre, sum_eq_sup, sup_comm]
    exact commute_with_add_dim ms_pre

  have ms_pre_le_Inf_borel : unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil) ≤ Inf_borel := by
    have h_le : unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel := h_ms_pre ▸ hΩ_pre.1
    exact unSplitTri_I_borel_le_Inf_borel ms_pre (ms_pre_le_pi_of_le_Inf_borel n ms_pre h_le)
  -- Construct the PSpace witness for the independent product
  let r_pspace : PSpace HC :=
    PSpace.mk'' μ' ms_pre_le_Inf_borel
  -- The measure product condition: under μ', sets from disjoint coordinates
  -- factor as a product. This is the key measure-theoretic fact:
  -- μ' = (μ_k × leb) ∘ (splitBi n)⁻¹ is a product measure, and sets measurable
  -- wrt ↓Ω_pre (first n coords) are independent from sets measurable wrt Ω_n (coord n).
  have h_measure_product :
      ∀ E (_ : MeasurableSet[(↓Ω_pre).ms] E)
        F (_ : MeasurableSet[Ω_n.ms] F),
        r_pspace.μ (E ∩ F) = (↓Ω_pre).μ E * Ω_n.μ F := by
    -- The proof connects PSpace measures to underlying measures and applies
    -- wp_unif_measure_product_core from MeasureProduct.lean.
    intro E hE F hF
    -- Decompose E: E = (fst ∘ splitBi n)⁻¹' A for some ms_pre-measurable A
    have hE' : MeasurableSet[unSplitBi (ms_pre ×ₘ Inf_nil)] E := h_ms_pre ▸ hE
    rw [unSplitBi_eq_comap_fst] at hE'
    obtain ⟨A, hA_pre, rfl⟩ := hE'
    -- Decompose F: F = (· n)⁻¹' B_I for some Borel B_I
    have hF' : MeasurableSet[N_nil_I_borel n] F := hF
    rw [N_nil_I_borel_eq_comap_coord] at hF'
    obtain ⟨B_I, hB_I, rfl⟩ := hF'
    -- ms_pre ≤ pi
    have h_ms_pre_le : unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel :=
      h_ms_pre ▸ hΩ_pre.1
    have h_pi := ms_pre_le_pi_of_le_Inf_borel n ms_pre h_ms_pre_le
    have hA_pi : @MeasurableSet _ MeasurableSpace.pi A := h_pi A hA_pre
    -- r_pspace.μ (E ∩ F) = μ'.1 (E ∩ F) via trim
    have hE_combined := pre_measurable_in_combined n ms_pre
      (show MeasurableSet[unSplitBi (ms_pre ×ₘ Inf_nil)] _ from by
        rw [unSplitBi_eq_comap_fst]; exact ⟨A, hA_pre, rfl⟩)
    have hF_combined := coord_measurable_in_combined n ms_pre
      (show MeasurableSet[N_nil_I_borel n] _ from by
        rw [N_nil_I_borel_eq_comap_coord]; exact ⟨B_I, hB_I, rfl⟩)
    have h_r : r_pspace.μ ((Prod.fst ∘ splitBi n) ⁻¹' A ∩ (· n) ⁻¹' B_I)
        = μ'.1 ((Prod.fst ∘ splitBi n) ⁻¹' A ∩ (· n) ⁻¹' B_I) :=
      trim_measurableSet_eq ms_pre_le_Inf_borel (hE_combined.inter hF_combined)
    -- (↓Ω_pre).μ E = μ.1 E via le_preserves_measure
    have h_pre : (↓Ω_pre).μ ((Prod.fst ∘ splitBi n) ⁻¹' A) =
        μ.1 ((Prod.fst ∘ splitBi n) ⁻¹' A) := by
      exact MeasureOnSpace.le_preserves_measure hΩ_pre (h_ms_pre ▸ by
        rw [unSplitBi_eq_comap_fst]; exact ⟨A, hA_pre, rfl⟩)
    -- Ω_n.μ F = μ'.1 F via trim
    have h_n : Ω_n.μ ((· n) ⁻¹' B_I) = μ'.1 ((· n) ⁻¹' B_I) := by
      change μ'.1.trim (N_nil_I_borel_le_Inf_borel n) _ = μ'.1 _
      exact trim_measurableSet_eq (N_nil_I_borel_le_Inf_borel n)
        (by rw [N_nil_I_borel_eq_comap_coord]; exact ⟨B_I, hB_I, rfl⟩)
    -- Core: μ'.1 (E ∩ F) = μ.1 E * leb.1 F
    have h_core := wp_unif_measure_product_core n μ hA_pi hB_I rfl rfl
    -- leb.1 F = Ω_n.μ F  (since both equal volume B_I)
    -- Use: Ω_n.μ = μ'.1.trim h, and trim_measurableSet_eq gives Ω_n.μ F = μ'.1 F
    -- And μ'.1 F = leb.1 F by product measure marginal
    -- μ'.1 F = leb.1 F: use wp_unif_measure_product_core with A = univ
    have h_μ'_eq_leb : μ'.1 ((· n) ⁻¹' B_I) =
        lebHC.toMeasure ((· n) ⁻¹' B_I) := by
      have h_univ := wp_unif_measure_product_core n μ
        (@MeasurableSet.univ _ MeasurableSpace.pi) hB_I
        (show @Set.univ HC = (Prod.fst ∘ splitBi n) ⁻¹' Set.univ from by simp) rfl
      simp only [Set.univ_inter] at h_univ
      rwa [show μ.1 (@Set.univ HC) = 1 from @measure_univ _ Inf_borel μ.1 μ.2, one_mul] at h_univ
    rw [h_r, h_core, h_pre]
    congr 1
    rw [← h_μ'_eq_leb, ← h_n]
  -- Assemble the independent product proof
  have h_indep : r_pspace =ᵢ (↓Ω_pre).1 ⊕ᵢ Ω_n.1 :=
    ⟨h_sum_eq.symm, h_measure_product⟩
  -- Show the PSp PCM operation is defined (∃! r, r =ᵢ p ⊕ᵢ q)
  -- We use PSpace.binop_eq_some_of_isIndependentProduct at the PSpace level,
  -- then lift to PSp via psp_val_binop.
  have h_pspace_binop : (↓Ω_pre).1 ⋆ Ω_n.1 = some r_pspace :=
    PSpace.Krm.binop_eq_some_of_isIndependentProduct h_indep
  have Ω_post : ✓'(↓Ω_pre ⋆ Ω_n) := by
    have h_map := PSp.psp_val_binop (↓Ω_pre) Ω_n
    rw [h_pspace_binop] at h_map
    cases h : (↓Ω_pre) ⋆ Ω_n with
    | some _ => rfl
    | none => simp [h] at h_map
  -- eq_Ω_post_ms: (↓Ω_post).1 = r_pspace (from psp_val_get), so ms agrees
  have h_val_eq : (↓Ω_post).1 = r_pspace := by
    rw [PSp.psp_val_get (↓Ω_pre) Ω_n Ω_post]
    have h1 := PSp.psp_isSome_val (↓Ω_pre) Ω_n Ω_post
    have h2 : ((↓Ω_pre).1 ⋆ Ω_n.1).get h1 = r_pspace :=
      Option.some_injective _ ((Option.some_get h1).trans h_pspace_binop)
    exact h2
  have eq_Ω_post_ms : (↓Ω_post).ms = unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil) := by
    show (↓Ω_post).1.ms = _
    rw [h_val_eq]; rfl
  -- The new resource
  have Ω' : ✓'(Ω ⋆ Ω_n) := right Ω_post
  -- have eq_Ω_post : ↓Ω_post = ↓Ω_post_alt :=
  --   Krm_helper.get_assoc_eq' Ω_fr Ω Ω_n Ω_pre Ω_post Ω' Ω_post_alt
  use X, ↓Ω', (assoc_right Ω_post), μ'

  refine ⟨?Ω_post_le, ?bind_eq, ?postcond⟩
  case Ω_post_le =>
    -- (↓Ω_post).toPSpace = r_pspace by uniqueness of the independent product.
    -- Step 1: The PSp binop relates to the PSpace binop via psp_val_binop.
    have h_psp_some : (↓Ω_pre) ⋆ Ω_n = some (↓Ω_post) :=
      (Option.some_get Ω_post).symm
    have h_pspace_post : (↓Ω_pre).toPSpace ⋆ Ω_n.toPSpace = some (↓Ω_post).toPSpace := by
      have h_map := PSp.psp_val_binop (↓Ω_pre) Ω_n
      rw [h_psp_some, Option.map_some] at h_map
      exact h_map.symm
    -- Step 2: By uniqueness, (↓Ω_post).toPSpace = r_pspace
    have h_Ω_post_eq_r : (↓Ω_post).toPSpace = r_pspace :=
      Option.some_injective _ (h_pspace_post.symm.trans h_pspace_binop)
    -- Step 3: r_pspace ≤ PSpace.mk' μ' because r_pspace = (PSpace.mk' μ').trim ...
    have h_r_le : r_pspace ≤ PSpace.mk' μ' := by
      -- r_pspace = PSpace.mk'' μ' le = ⟨⟨ms_combined, μ'.1.trim le⟩, ...⟩
      -- PSpace.mk' μ' = ⟨⟨Inf_borel, μ'.1⟩, μ'.2⟩
      -- (PSpace.mk' μ').trim le = ⟨⟨ms_combined, μ'.1.trim le⟩, ...⟩ = r_pspace
      -- And trim_le gives the result.
      have : r_pspace = (PSpace.mk' μ').trim ms_pre_le_Inf_borel := by
        apply PSpace.ext_ms
        · rfl
        · intro E hE
          rfl
      rw [this]
      exact PSpace.trim_le ms_pre_le_Inf_borel

    exact (assoc_right_eq Ω_post).symm ▸ h_Ω_post_eq_r.symm ▸ h_r_le

  case bind_eq =>
    -- LHS kernel is `const HC unif01_sem ×ₖ det D_ext`
    have h_lhs_kernel : toMK (Term.unif01.den ∘ᵣ D).toMeasurableFun =
        Kernel.const HC Appl.unif01_sem := by
      ext ω s hs; simp [toMK, Term.den, Appl.unif01_sem, Kernel.const]; rfl
    rw [h_lhs_kernel]
    -- LHS is `unif01_sem.prod (μ.map D_ext)`
    rw [const_prod_det_compMeasure]
    -- RHS is `μ'.map (fun ω => (X ω, D_ext ω))`
    rw [det_prod_det_compMeasure]
    -- `μ'.map (fun ω => (X ω, D_ext ω)) = unif01_sem.prod (μ.map D_ext)`
    exact (map_X_Dext_eq_prod μ D_ext (le_max_right n₁ n₂) μ_k rfl μ' rfl).symm

  case postcond =>
    -- Q X via wand elimination
    dsimp only [BIBase.forall, BIBase.sForall] at lhs
    have h_wand := lhs iprop(X ∼ unif01_sem -∗ Q X) ⟨X, rfl⟩
    have X_dist : unif01_sem = Measure.bind Ω_n.μ (fun ω ↦ Measure.dirac (X ω)) := by
      -- Unfold X to get (fun ω ↦ ↑(ω n)) and Ω_n.μ to μ'.1.trim
      change unif01_sem = @Measure.bind _ _ (N_nil_I_borel n) _
        (μ'.1.trim (N_nil_I_borel_le_Inf_borel n))
        (fun ω ↦ Measure.dirac (↑(ω n) : ℝ))
      rw [bind_dirac_trim_eq_map_orig (HC.coordProj_measurable n) μ'.1
          (N_nil_I_borel_le_Inf_borel n)]
      letI : MeasurableSpace (Fin n → I) := MeasurableSpace.pi
      have hμ' : (↑μ' : Measure (ℕ → I)) =
          Measure.map (↑(splitBi n).symm) ↑(μ_k.prod lebHC) := by
        rw [ProbabilityMeasure.toMeasure_map]
      exact unif01_eq_map_coord_prod n μ_k μ' hμ'
    have X_meas : @Measurable HC ⟪Ty.real⟫ Ω_n.ms _ X := HC.coordProj_measurable n
    have h_qx := h_wand Ω_n ((Pcm.comm Ω Ω_n) ▸ Ω') ⟨X_meas, X_dist⟩
    suffices h : ↓((Pcm.comm Ω Ω_n) ▸ Ω') = ↓Ω' by exact h ▸ h_qx
    exact Krm.get_comm Ω_n Ω ((Pcm.comm Ω Ω_n) ▸ Ω') Ω'

end
end WP
