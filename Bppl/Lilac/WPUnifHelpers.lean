/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Bppl.Lilac.Appl
import Bppl.Lilac.MeasureProduct

/-! # Helper lemmas for `wp_unif` (B.21)

These lemmas are placed in a separate file to avoid circular dependencies with
the Iris proof mode imports used in `ProofRules.lean`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open HC MeasureTheory unitInterval Appl

noncomputable section

/-! ### `Measure.bind ∘ dirac` on a trimmed measure equals `Measure.map` on the original -/

/-
For a function `f` that is `ms'`-measurable, `Measure.bind (μ.trim h) (dirac ∘ f)` equals
`Measure.map f μ`, where both sides produce a `Measure β`. The key point is that the bind
uses the trimmed σ-algebra `ms'`, but the result agrees with `map f μ` (using `ms`).
-/
lemma bind_dirac_trim_eq_map_orig {α β : Type*}
    {ms ms' : MeasurableSpace α} [MeasurableSpace β]
    {f : α → β} (hf : @Measurable α β ms' _ f) (μ : @Measure α ms) (h : ms' ≤ ms) :
    @Measure.bind α β ms' _ (μ.trim h) (fun ω ↦ Measure.dirac (f ω)) =
      @Measure.map α β ms _ f μ := by
        ext s hs;
        -- Apply the lemma that the bind of a Dirac measure is the map of the function.
        have h_bind_dirac : (μ.trim h).bind (fun ω => Measure.dirac (f ω)) = Measure.map f (μ.trim h) := by
          apply Measure.bind_dirac_eq_map;
          grind;
        rw [ h_bind_dirac, Measure.map_apply, Measure.map_apply ];
        · rw [ MeasureTheory.trim_measurableSet_eq h ];
          exact hf hs;
        · exact hf.mono h le_rfl;
        · exact hs;
        · exact hf;
        · exact hs

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

/-- The `bind ∘ dirac` of the trimmed product measure under `fun ω ↦ ↑(ω n)` equals
`unif01_sem`. -/
lemma WP.X_dist_helper (n : ℕ)
    (leb : @ProbabilityMeasure (ℕ → I) Inf_borel)
    (h_leb : leb.1 = Measure.infinitePiNat (fun _ =>
      (MeasureTheory.MeasureSpace.volume : Measure I))) :
    let μ_trim := leb.1.trim (N_nil_I_borel_le_Inf_borel n)
    unif01_sem =
      @Measure.bind (ℕ → I) ℝ (N_nil_I_borel n) _
        μ_trim (fun ω ↦ Measure.dirac (↑(ω n) : ℝ)) := by
  intro μ_trim
  rw [bind_dirac_trim_eq_map_orig (HC.coordProj_measurable n) leb.1
    (N_nil_I_borel_le_Inf_borel n)]
  -- Now: unif01_sem = @Measure.map ... Inf_borel _ (fun ω ↦ ↑(ω n)) leb.1
  show unif01_sem = @Measure.map (ℕ → I) ℝ Inf_borel _ (fun ω ↦ (↑(ω n) : ℝ)) leb.1
  rw [coord_val_eq_comp]
  rw [show @Measure.map (ℕ → I) ℝ Inf_borel _ (Subtype.val ∘ (· n)) leb.1 =
    Measure.map Subtype.val (@Measure.map (ℕ → I) I Inf_borel _ (· n) leb.1) from
    (Measure.map_map measurable_subtype_coe (measurable_pi_apply n)).symm]
  rw [h_leb, infinitePiNat_coord_map n]
  rfl

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
    (fun ω : ℕ → I => (↑(ω n) : ℝ)) ∘ (splitBi n).symm =
    (fun p : (Fin n → I) × (ℕ → I) => (↑(p.2 0) : ℝ)) := by
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
/-
The map of the n-th coordinate projection under the product measure
`(μ_k.prod leb).map (splitBi n).symm` equals `Measure.map Subtype.val volume`.
This is the core measure-theoretic fact for the `bind_eq` case of `wp_unif`.
-/
lemma unif01_eq_map_coord_prod (n : ℕ)
    (μ_k : ProbabilityMeasure (Fin n → I))
    (μ' : ProbabilityMeasure (ℕ → I))
    (hμ' : (↑μ' : Measure (ℕ → I)) =
      Measure.map (↑(splitBi n).symm) ↑(μ_k.prod lebHC)) :
    Measure.map Subtype.val (volume : Measure I) =
      Measure.map (fun ω : ℕ → I => (↑(ω n) : ℝ)) ↑μ' := by
  rw [ hμ', Measure.map_map ];
  · rw [ coord_comp_splitBi_symm ];
    have h_volume : Measure.map (fun p : (Fin n → I) × (ℕ → I) => p.2 0)
        (μ_k.prod lebHC).toMeasure =
        Measure.map (fun p : ℕ → I => p 0) lebHC.toMeasure := by
      ext s hs;
      rw [ Measure.map_apply, Measure.map_apply ];
      · rw [ ProbabilityMeasure.toMeasure_prod ];
        rw [ MeasureTheory.Measure.prod_apply ];
        · simp +decide [ Set.preimage ];
        · exact measurable_pi_apply 0 hs |> MeasurableSet.preimage <| measurable_snd;
      · exact measurable_pi_apply 0;
      · exact hs;
      · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd;
      · exact hs;
    convert congr_arg ( fun m => Measure.map Subtype.val m ) h_volume.symm using 1;
    · have h_leb : (lebHC.toMeasure : Measure (ℕ → I)) =
        Measure.infinitePiNat (fun _ => volume) := rfl
      rw [ h_leb, map_eval_zero_infinitePiNat ];
    · rw [ Measure.map_map ];
      · rfl;
      · exact measurable_subtype_coe;
      · fun_prop;
  · fun_prop;
  · exact MeasurableEquiv.measurable _

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
equals `unif01_sem`. -/
lemma leb_coord_preimage_eq_unif01
    (n : ℕ) (E : Set ℝ) (hE : MeasurableSet E) :
    lebHC.toMeasure ((· n : HC → I) ⁻¹' (Subtype.val ⁻¹' E)) = Appl.unif01_sem E := by
  rw [Appl.unif01_sem, MeasureTheory.Measure.map_apply]
  · convert infinitePiNat_coord_marginal n (Subtype.val ⁻¹' E) _ using 1
    exact measurable_subtype_coe hE
  · exact measurable_subtype_coe
  · exact hE

/-- The pushforward of μ' under `(X, D_ext)` equals `unif01_sem.prod (μ.map D_ext)`. -/
lemma map_X_Dext_eq_prod
    (μ : @ProbabilityMeasure HC Inf_borel)
    (D : RV α)
    {n : ℕ} (hn : D.n ≤ n)
    (μ_k : ProbabilityMeasure (Fin n → I))
    (hμ_k : μ_k = μ.map (measurable_fst.comp (splitBi n).measurable).aemeasurable)
    (μ' : @ProbabilityMeasure HC Inf_borel)
    (hμ' : μ' = (μ_k.prod lebHC).map (splitBi n).symm.measurable.aemeasurable) :
    μ'.1.map (fun ω => ((↑(ω n) : ℝ), D.toFun ω)) =
    Appl.unif01_sem.prod (μ.1.map D.toFun) := by
  have : IsProbabilityMeasure (μ.1.map D.toFun) :=
    @Measure.isProbabilityMeasure_map _ _ _ _ μ.1 μ.2 _ D.meas.aemeasurable
  symm; apply Measure.prod_eq
  intro E F hE hF
  -- Reduce to the rectangle case via `fp_preimage_form`, then apply the measure-product core.
  obtain ⟨A, hA⟩ := ff_preimage_form D hn F hF
  have hE' : MeasurableSet (Subtype.val ⁻¹' E : Set I) := measurable_subtype_coe hE
  refine .trans
    ?lhs_eq (
    (wp_unif_measure_product_core n μ (E := (Prod.fst ∘ splitBi n) ⁻¹' A)
      (F := (· n) ⁻¹' (Subtype.val ⁻¹' E)) hA.1 hE' rfl rfl).trans
    ?rhs_eq)
  case lhs_eq =>
    -- `μ'.1.map (X, D_ext) (E ×ˢ F)` is `μ'.1` of the preimage rectangle.
    convert Measure.map_apply _ _ using 2
    · simp [hμ', hμ_k]
    · grind
    · exact Measurable.prodMk (measurable_subtype_coe.comp (measurable_pi_apply n)) D.meas
    · exact hE.prod hF
  case rhs_eq =>
    -- `μ.1 (preimage A) = (μ.map D_ext) F` and `infinitePiNat (coord ⁻¹' …) = unif01_sem E`.
    rw [← hA.2, Measure.map_apply]
    · rw [mul_comm, leb_coord_preimage_eq_unif01]
      exact hE
    · exact D.meas
    · exact hF
