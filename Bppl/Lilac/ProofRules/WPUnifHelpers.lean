/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Bppl.Lilac.Appl
import Bppl.Lilac.ProofRules.MeasureProduct

/-! # Helper lemmas for WP Meas

To be consolidated into `WPMeas.lean`

-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open HC MeasureTheory unitInterval Appl

/- For a function `f` that is `ms'`-measurable, `Measure.map f (μ.trim h)` equals
`Measure.map f μ`. The trimmed and original measures agree on `ms'`-measurable sets, and
preimages under `f` are `ms'`-measurable, so the pushforwards coincide.  -/
lemma map_trim_eq_map {α β : Type*}
    {ms ms' : MeasurableSpace α} [MeasurableSpace β]
    {f : α → β} (hf : @Measurable α β ms' _ f) (μ : @Measure α ms) (h : ms' ≤ ms) :
    @Measure.map α β ms' _ f (μ.trim h) = @Measure.map α β ms _ f μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply (hf.mono h le_rfl) hs,
      MeasureTheory.trim_measurableSet_eq h (hf hs)]

/- The n-th coordinate of `(splitBi n).symm (a, b)` equals `b 0`.  -/
lemma splitBi_symm_apply_self (n : ℕ) (a : Fin n → I) (b : ℕ → I) :
    ((splitBi n).symm (a, b)) n = b 0 := by
  unfold splitBi
  simp [MeasurableEquiv.sumPiEquivProdPi, finSumNatEquiv, MeasurableEquiv.piCongrLeft,
    Equiv.sumPiEquivProdPi, MeasurableEquiv.trans, Equiv.piCongrLeft]

/- Splitting then projecting is projecting then splitting. -/
lemma coord_comp_splitBi_symm (n : ℕ) :
    (fun ω : ℕ → I ↦ ω n) ∘ (splitBi n).symm = (fun p : (Fin n → I) × (ℕ → I) => p.2 0) :=
  funext fun p => splitBi_symm_apply_self n p.1 p.2

/- The 0th marginal of an infinite product of identical probability measures
is one of those measures. -/
lemma map_eval_zero_infinitePiNat {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Measure.map (fun f : ℕ → X => f 0) (Measure.infinitePiNat (fun _ => μ)) = μ := by
  change Measure.map (MeasurableEquiv.funUnique _ _ ∘ ({0} : Finset ℕ).restrict)
    (Measure.infinitePiNat fun _ => μ) = μ
  rw [← Measure.map_map (f := ({0} : Finset ℕ).restrict (π := fun _ => X))
        (MeasurableEquiv.measurable _) (Finset.measurable_restrict _),
      Measure.infinitePiNat_map_restrict]
  exact (measurePreserving_funUnique μ ({0} : Finset ℕ)).map_eq

/- The map of the n-th coordinate projection under the product measure
`(μ_k.prod leb).map (splitBi n).symm` equals `lebI`.
This is the core measure-theoretic fact for the `bind_eq` case of `wp_meas`.  -/
lemma unif01_eq_map_coord_prod (n : ℕ)
    (μ_k : ProbabilityMeasure (Fin n → I))
    (μ' : ProbabilityMeasure (ℕ → I))
    (hμ' : (↑μ' : Measure (ℕ → I)) = Measure.map (↑(splitBi n).symm) ↑(μ_k.prod lebHC))
    : lebI = Measure.map (λ ω : ℕ → I ↦ ω n) ↑μ' := by
  rw [hμ', Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rw [coord_comp_splitBi_symm]
  have h_volume : (μ_k.prod lebHC).toMeasure.map (fun p : (Fin n → I) × (ℕ → I) => p.2 0)
      = lebHC.1.map (fun p : ℕ → I => p 0) := by
    ext s hs
    rw [Measure.map_apply (measurable_pi_apply 0) hs, Measure.map_apply (by fun_prop) hs]
    rw [ProbabilityMeasure.toMeasure_prod, MeasureTheory.Measure.prod_apply (by measurability)]
    simp [Set.preimage]
  rw [h_volume]
  change lebI = (Measure.infinitePiNat (fun _ => lebI)).map (fun p : ℕ → I ↦ p 0)
  rw [map_eval_zero_infinitePiNat]

open ProbabilityTheory ProbabilityTheory.Kernel

/-! ### General kernel-measure lemmas -/
variable {α β γ : Type*} [msα : MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Product of two deterministic kernels composed with a measure gives a pushforward. -/
lemma det_prod_det_compMeasure (g : α → β) (hg : Measurable g) (f : α → γ) (hf : Measurable f)
    (μ : Measure α) [SFinite μ] :
    (deterministic g hg ×ₖ deterministic f hf) ∘ₘ μ = μ.map (fun a => (g a, f a)) := by
  convert (Measure.deterministic_comp_eq_map (hg.prodMk hf))
  ext; simp [deterministic_prod_deterministic]

/-- Composing `(const ν ×ₖ det f)` with a measure gives a product measure. -/
lemma const_prod_det_compMeasure
    (ν : Measure β) [SigmaFinite ν]
    (f : α → γ) (hf : Measurable f) (μ : Measure α) [IsProbabilityMeasure μ] :
    (const α ν ×ₖ deterministic f hf) ∘ₘ μ = ν.prod (μ.map f) := by
  grind +suggestions

/-! ### Finite footprint helpers -/
open HC

noncomputable abbrev RV.n (D : RV α) : ℕ := D.ff.choose

/-- If `D : RV α` has finite footprint of size `D.n` and `D.n ≤ n`, then `D ⁻¹' E` can be
written as `(Prod.fst ∘ splitBi n) ⁻¹' A` for some pi-measurable `A`. -/
lemma ff_preimage_form (D : RV α) {n : ℕ} (hn : D.n ≤ n)
    (E : Set α) (hE : MeasurableSet E) :
    ∃ A : Set (Fin n → I), MeasurableSet A ∧
      D.toFun ⁻¹' E = (Prod.fst ∘ splitBi n) ⁻¹' A := by
  obtain ⟨ms_n, hms_n⟩ := HC.finite_footprint_of_ge hn D.ff.choose_spec
  have h_preimage_measurable :
      MeasurableSet[_root_.MeasurableSpace.comap D.toFun ‹MeasurableSpace α›]
        (D.toFun ⁻¹' E) :=
    ⟨E, hE, rfl⟩
  rw [hms_n, unSplitBi_eq_comap_fst] at h_preimage_measurable
  obtain ⟨A, hA, hA'⟩ := h_preimage_measurable
  refine ⟨A, ?_, hA'.symm⟩
  apply ms_pre_le_pi_of_le_Inf_borel n ms_n
  · exact hms_n ▸ D.meas.comap_le
  · convert hA using 1
