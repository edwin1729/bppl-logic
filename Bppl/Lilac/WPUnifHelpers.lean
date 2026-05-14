/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Mathlib
import Bppl.Lilac.HilbertCube

/-! # Helper lemmas for `wp_unif` (B.21)

These lemmas are placed in a separate file to avoid circular dependencies with
the Iris proof mode imports used in `ProofRules.lean`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open HC MeasureTheory unitInterval

noncomputable section

/-- The semantic (native lean) uniform distribution in the interval [0,1].

This is the pushforward of Lebesgue measure on `I = Set.Icc 0 1`
via the subtype coercion `↑ : I → ℝ`. -/
def WP.unif01_sem : Measure ℝ :=
  Measure.map Subtype.val (MeasureTheory.MeasureSpace.volume (α := Set.Icc (0 : ℝ) 1))

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
    WP.unif01_sem =
      @Measure.bind (ℕ → I) ℝ (N_nil_I_borel n) _
        μ_trim (fun ω ↦ Measure.dirac (↑(ω n) : ℝ)) := by
  intro μ_trim
  rw [bind_dirac_trim_eq_map_orig (HC.coordProj_measurable n) leb.1
    (N_nil_I_borel_le_Inf_borel n)]
  -- Now: unif01_sem = @Measure.map ... Inf_borel _ (fun ω ↦ ↑(ω n)) leb.1
  show WP.unif01_sem = @Measure.map (ℕ → I) ℝ Inf_borel _ (fun ω ↦ (↑(ω n) : ℝ)) leb.1
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
    (leb : ProbabilityMeasure (ℕ → I))
    (hleb : (↑leb : Measure (ℕ → I)) = Measure.infinitePiNat (fun _ => volume))
    (μ' : ProbabilityMeasure (ℕ → I))
    (hμ' : (↑μ' : Measure (ℕ → I)) =
      Measure.map (↑(splitBi n).symm) ↑(μ_k.prod leb)) :
    Measure.map Subtype.val (volume : Measure I) =
      Measure.map (fun ω : ℕ → I => (↑(ω n) : ℝ)) ↑μ' := by
  rw [ hμ', Measure.map_map ];
  · rw [ coord_comp_splitBi_symm ];
    -- The measure on the second component is the volume measure.
    have h_volume : Measure.map (fun p : (Fin n → I) × (ℕ → I) => p.2 0) (μ_k.prod leb).toMeasure = Measure.map (fun p : ℕ → I => p 0) leb.toMeasure := by
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
    · rw [ hleb, map_eval_zero_infinitePiNat ];
    · rw [ Measure.map_map ];
      · rfl;
      · exact measurable_subtype_coe;
      · fun_prop;
  · fun_prop;
  · exact MeasurableEquiv.measurable _
