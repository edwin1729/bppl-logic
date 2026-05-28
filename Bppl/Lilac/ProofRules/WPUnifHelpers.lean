/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Bppl.Lilac.Appl
import Bppl.Lilac.ProofRules.MeasureProduct

/-! # Helper lemmas for `wp_unif` (B.21)

These lemmas are placed in a separate file to avoid circular dependencies with
the Iris proof mode imports used in `ProofRules.lean`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open HC MeasureTheory unitInterval Appl

noncomputable section

/-! ### `Measure.map` on a trimmed measure equals `Measure.map` on the original -/

/-
For a function `f` that is `ms'`-measurable, `Measure.map f (μ.trim h)` equals
`Measure.map f μ`. The trimmed and original measures agree on `ms'`-measurable sets, and
preimages under `f` are `ms'`-measurable, so the pushforwards coincide.
-/
lemma map_trim_eq_map {α β : Type*}
    {ms ms' : MeasurableSpace α} [MeasurableSpace β]
    {f : α → β} (hf : @Measurable α β ms' _ f) (μ : @Measure α ms) (h : ms' ≤ ms) :
    @Measure.map α β ms' _ f (μ.trim h) = @Measure.map α β ms _ f μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply (hf.mono h le_rfl) hs,
      MeasureTheory.trim_measurableSet_eq h (hf hs)]

/-! ### The `n`-th coordinate marginal of the infinite product measure -/

/-
The pushforward of `infinitePiNat (fun _ => volume)` under `(· n)` equals `volume`.
This is the standard marginal property of product measures.
-/
lemma infinitePiNat_coord_map (n : ℕ) :
    @Measure.map (ℕ → I) I Inf_borel _ (· n)
      (Measure.infinitePiNat (fun _ => (MeasureTheory.MeasureSpace.volume : Measure I))) =
    MeasureTheory.MeasureSpace.volume := by
      ext T hT;
      -- The measure of the preimage of T under the projection map is the same as the measure of T because the projection map is just picking out the nth coordinate.
      have h_preimage : (Measure.infinitePiNat (fun _ => volume)) (Set.preimage (fun x : ℕ → I => x n) T) = (Measure.pi (fun _ : Fin 1 => volume)) (Set.pi Set.univ (fun _ : Fin 1 => T)) := by
        have := @Measure.infinitePiNat_map_restrict;
        specialize @this ( fun _ => I ) ( fun _ => inferInstance ) ( fun _ => volume ) ( by infer_instance ) { n } ; simp_all +decide [ Set.preimage ] ;
        convert congr_arg ( fun m => m ( Set.pi Set.univ fun _ => T ) ) this using 1;
        · rw [ Measure.map_apply ];
          · congr with x ; simp +decide [ Set.preimage ];
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi fun _ => hT;
        · erw [ MeasureTheory.Measure.pi_pi ] ; aesop;
      rw [ MeasureTheory.Measure.map_apply ];
      · aesop;
      · exact measurable_pi_apply n;
      · exact hT

/-! ### `Measure.map` factors through `Subtype.val` and coordinate projection -/

/-- `fun ω ↦ ↑(ω n)` factors as `Subtype.val ∘ (· n)`. -/
lemma coord_val_eq_comp (n : ℕ) :
    (fun ω : ℕ → I ↦ (↑(ω n) : ℝ)) = Subtype.val ∘ (· n) := by
  ext; rfl

end

/-
The n-th coordinate of `(splitBi n).symm (a, b)` equals `b 0`.
-/
lemma splitBi_symm_apply_self (n : ℕ) (a : Fin n → I) (b : ℕ → I) :
    ((splitBi n).symm (a, b)) n = b 0 := by
  unfold splitBi;
  simp +decide [ MeasurableEquiv.sumPiEquivProdPi, finSumNatEquiv ];
  simp +decide [ MeasurableEquiv.piCongrLeft, Equiv.sumPiEquivProdPi ];
  simp +decide [ MeasurableEquiv.trans, Equiv.piCongrLeft ]
/-
The composition `(fun ω => (↑(ω n) : ℝ)) ∘ (splitBi n).symm`
equals `(fun p => (↑(p.2 0) : ℝ))`.
-/
lemma coord_comp_splitBi_symm (n : ℕ) :
    (fun ω : ℕ → I ↦ ω n) ∘ (splitBi n).symm =
    (fun p : (Fin n → I) × (ℕ → I) => p.2 0) := by
  exact funext fun p => splitBi_symm_apply_self n p.1 p.2 ▸ rfl
/-
The 0th marginal of an infinite product of identical probability measures
is the factor measure.
-/
lemma map_eval_zero_infinitePiNat {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Measure.map (fun f : ℕ → X => f 0) (Measure.infinitePiNat (fun _ => μ)) = μ := by
  convert MeasurePreserving.map_eq ( measurePreserving_funUnique μ ( { 0 } : Finset ℕ ) ) using 1;
  convert Measure.map_map ?_ ?_ using 1;
  convert Measure.infinitePiNat_map_restrict ( fun _ => μ ) { 0 } using 1;
  any_goals exact measurable_id;
  · constructor <;> intro h;
    · convert Measure.infinitePiNat_map_restrict ( fun _ => μ ) { 0 } using 1;
    · convert congr_arg ( Measure.map ( fun f : { x : ℕ // x ∈ { 0 } } → X => f ⟨ 0, by simp +decide ⟩ ) ) h using 1;
      · rw [ Measure.map_map ];
        · congr! 1;
        · exact measurable_pi_apply _;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · rw [ Measure.map_map ];
        · congr! 1;
        · exact measurable_pi_apply _;
        · exact measurable_id;
  · exact MeasurableEquiv.measurable _

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
/-- Composing a deterministic kernel with a measure gives the pushforward. -/
lemma det_compMeasure_eq_map {f : α → γ} (hf : Measurable f)
    (μ : Measure α) [SFinite μ] :
    (deterministic f hf) ∘ₘ μ = μ.map f := Measure.deterministic_comp_eq_map hf

/-- Product of two deterministic kernels composed with a measure gives a pushforward. -/
lemma det_prod_det_compMeasure
    (g : α → β) (hg : Measurable g) (f : α → γ) (hf : Measurable f)
    (μ : Measure α) [SFinite μ] :
    (deterministic g hg ×ₖ deterministic f hf) ∘ₘ μ =
    μ.map (fun a => (g a, f a)) := by
  convert (det_compMeasure_eq_map (hg.prodMk hf) μ)
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

/-- The n-th coordinate marginal of the i.i.d. product under `Subtype.val` preimage
equals `lebI`. -/
lemma leb_coord_preimage_eq_unif01
    (n : ℕ) (E : Set I) (hE : MeasurableSet E) :
    lebHC.toMeasure ((· n : HC → I) ⁻¹' E) = lebI E := by
  convert infinitePiNat_coord_marginal n E _ using 1
  exact hE
