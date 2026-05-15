/-
Helper lemmas for the measure product condition in wp_unif.
This file is separated to avoid Iris dependencies.
-/
import Mathlib
import Bppl.Lilac.KRM

open MeasureTheory MeasurableSpace HC unitInterval

noncomputable section

set_option autoImplicit true

/-! ### Measurability sub-lemmas -/

lemma inter_measurable_in_combined (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I))
    {E F : Set HC}
    (hE : MeasurableSet[unSplitBi (ms_pre ×ₘ Inf_nil)] E)
    (hF : MeasurableSet[N_nil_I_borel n] F) :
    MeasurableSet[unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)] (E ∩ F) := by
  apply MeasurableSet.inter
  · exact (commute_over_equiv4 ms_pre ▸ le_sup_right : unSplitBi _ ≤ _) _ hE
  · exact (commute_over_equiv4 ms_pre ▸ le_sup_left : N_nil_I_borel n ≤ _) _ hF

lemma pre_measurable_in_combined (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I))
    {E : Set HC}
    (hE : MeasurableSet[unSplitBi (ms_pre ×ₘ Inf_nil)] E) :
    MeasurableSet[unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)] E :=
  (commute_over_equiv4 ms_pre ▸ le_sup_right : unSplitBi _ ≤ _) _ hE

lemma coord_measurable_in_combined (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I))
    {F : Set HC}
    (hF : MeasurableSet[N_nil_I_borel n] F) :
    MeasurableSet[unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)] F :=
  (commute_over_equiv4 ms_pre ▸ le_sup_left : N_nil_I_borel n ≤ _) _ hF

/-! ### σ-algebra characterization -/

/-- `unSplitBi (ms_pre ×ₘ Inf_nil)` is the comap of `ms_pre` through `fst ∘ splitBi n`. -/
lemma unSplitBi_eq_comap_fst (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I)) :
    unSplitBi (ms_pre ×ₘ Inf_nil) = ms_pre.comap (Prod.fst ∘ splitBi n) := by
  simp only [unSplitBi, Inf_nil, MeasurableSpace.prod, MeasurableSpace.comap_bot,
    sup_bot_eq, MeasurableSpace.comap_comp]

/-! ### Helper lemmas for the product factorization -/

/-- `splitBi n` second component at index `k` gives `ω (n + k)`. -/
lemma splitBi_snd_apply (n : ℕ) (ω : HC) (k : ℕ) : (splitBi n ω).2 k = ω (n + k) := by
  simp [splitBi, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]

/-- The middle component of `splitTri n ω` is `ω n`. -/
lemma splitTri_snd_fst (n : ℕ) (ω : HC) : (splitTri n ω).2.1 = ω n := by
  simp [splitTri, splitBi, splitOne, MeasurableEquiv.piCongrLeft,
        MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.funUnique,
        Equiv.natEquivNatSumPUnit, Equiv.sumComm, MeasurableEquiv.prodCongr,
        Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]

/-
`N_nil_I_borel n` is the comap of `I_borel` through `(· n)`.
-/
lemma N_nil_I_borel_eq_comap_coord (n : ℕ) :
    N_nil_I_borel n = (inferInstance : MeasurableSpace I).comap (· n : HC → I) := by
  -- By definition of `splitTri`, we know that `splitTri n` is the composition of `splitBi n` and `splitOne`.
  have h_splitTri : splitTri n = (splitBi n).trans ((MeasurableEquiv.refl (Fin n → I)).prodCongr splitOne) := by
    -- By definition of `splitTri`, we have `splitTri n = (splitBi n).trans ((MeasurableEquiv.refl (Fin n → I)).prodCongr splitOne)`.
    simp [splitTri];
  unfold N_nil_I_borel;
  simp +decide [ h_splitTri, MeasurableSpace.prod ];
  congr! 1

/-
If `unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel`, then `ms_pre ≤ pi`.
-/
lemma ms_pre_le_pi_of_le_Inf_borel (n : ℕ) (ms_pre : MeasurableSpace (Fin n → I))
    (h : unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel) :
    ms_pre ≤ (MeasurableSpace.pi : MeasurableSpace (Fin n → I)) := by
  contrapose! h;
  simp_all +decide [ MeasurableSpace.comap_le_iff_le_map ];
  intro H;
  refine' h _;
  intro s hs;
  convert H _ ( MeasurableSet.prod hs MeasurableSet.univ ) using 1;
  constructor <;> intro h;
  · exact MeasurableSet.prod h MeasurableSet.univ;
  · convert h.preimage _;
    rotate_left;
    exact fun x => ( x, fun _ => 0 );
    · exact measurable_id.prodMk measurable_const;
    · aesop

/-- `(splitBi n).symm ⁻¹' ((Prod.fst ∘ splitBi n) ⁻¹' A) = Prod.fst ⁻¹' A`. -/
lemma splitBi_symm_preimage_fst (n : ℕ) (A : Set (Fin n → I)) :
    (splitBi n).symm ⁻¹' ((Prod.fst ∘ splitBi n) ⁻¹' A) = Prod.fst ⁻¹' A := by
  rw [Set.preimage_comp]
  exact (splitBi n).symm_preimage_preimage _

/-
`(splitBi n).symm ⁻¹' ((· n) ⁻¹' B) = Prod.snd ⁻¹' ((· 0) ⁻¹' B)`.
-/
lemma splitBi_symm_preimage_coord_n (n : ℕ) (B : Set I) :
    (splitBi n).symm ⁻¹' ((· n : HC → I) ⁻¹' B) =
    Prod.snd ⁻¹' ((· 0 : HC → I) ⁻¹' B) := by
  ext ⟨a, b⟩; simp [splitBi];
  unfold MeasurableEquiv.sumPiEquivProdPi MeasurableEquiv.piCongrLeft;
  unfold MeasurableEquiv.trans; simp +decide [ Equiv.symm_apply_eq ] ;
  unfold Equiv.piCongrLeft; simp +decide [ Equiv.piCongrLeft ] ;

/-
For the i.i.d. product measure, the k-th marginal equals `volume`.
-/
lemma infinitePiNat_coord_marginal (k : ℕ) (B : Set I) (hB : MeasurableSet B) :
    Measure.infinitePiNat (fun _ => (volume : Measure I)) ((· k : HC → I) ⁻¹' B) =
    volume B := by
  have h_restrict : (Measure.infinitePiNat fun _ => volume).map (Finset.restrict {k} : HC → ({k} : Finset ℕ) → I) = Measure.pi (fun _ : ({k} : Finset ℕ) => volume) := by
    exact?;
  convert congr_arg ( fun μ => μ ( ( fun x => x ⟨ k, by simp +decide ⟩ ) ⁻¹' B ) ) h_restrict using 1;
  · rw [ Measure.map_apply ];
    · congr! 1;
    · fun_prop;
    · exact measurable_pi_apply _ hB;
  · erw [ show ( fun x : ( { k } : Finset ℕ ) → I => x ⟨ k, by simp +decide ⟩ ) ⁻¹' B = ( Set.pi Set.univ fun _ => B ) from ?_ ];
    · erw [ MeasureTheory.Measure.pi_pi ] ; aesop;
    · grind

/-! ### The main factorization -/

/-
Core computation for `wp_unif_measure_product`, separated to avoid instance conflicts
with `ms_pre`. Here `A` and `B_I` are measurable in the standard (pi/Borel) instances.
-/
lemma wp_unif_measure_product_core
    (n : ℕ) (μ : @ProbabilityMeasure HC Inf_borel)
    {E F : Set HC} {A : Set (Fin n → I)} {B_I : Set I}
    (hA_pi : MeasurableSet A) (hB_I : MeasurableSet B_I)
    (hE_eq : E = (Prod.fst ∘ splitBi n) ⁻¹' A)
    (hF_eq : F = (· n : HC → I) ⁻¹' B_I) :
    ((μ.map (measurable_fst.comp (HC.splitBi n).measurable).aemeasurable |>.prod
      ⟨Measure.infinitePiNat (fun _ => (volume : Measure I)), inferInstance⟩).map
      (HC.splitBi n).symm.measurable.aemeasurable).1 (E ∩ F) =
    μ.1 E * (Measure.infinitePiNat (fun _ => (volume : Measure I))) F := by
  simp_all +decide [ ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod, Measure.map_apply, MeasurableEquiv.map_apply ];
  rw [ show ( splitBi n ).symm ⁻¹' ( Prod.fst ∘ ⇑ ( splitBi n ) ⁻¹' A ) ∩ ( splitBi n ).symm ⁻¹' ( ( fun x => x n ) ⁻¹' B_I ) = A ×ˢ ( ( fun x => x 0 ) ⁻¹' B_I ) from ?_ ];
  · rw [ Measure.prod_prod, Measure.map_apply ];
    · rw [ infinitePiNat_coord_marginal, infinitePiNat_coord_marginal ];
      · exact hB_I;
      · exact hB_I;
    · fun_prop;
    · exact hA_pi;
  · ext ⟨x, y⟩; simp [splitBi_symm_preimage_fst, splitBi_symm_preimage_coord_n]

end
