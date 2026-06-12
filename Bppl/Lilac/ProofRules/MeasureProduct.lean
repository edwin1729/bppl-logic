/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Std
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
Helper lemmas for the measure product condition in `wp_meas`. Yet to be refactored
-/

open MeasureTheory MeasurableSpace HC unitInterval

noncomputable section

/-! ### Measurability sub-lemmas -/

lemma pre_measurable_in_combined (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I))
    {E : Set HC}
    (hE : MeasurableSet[unSplitBi (ms_pre ×ₘ Inf_nil)] E) :
    MeasurableSet[unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)] E :=
  (commute_with_add_dim ms_pre ▸ le_sup_right : unSplitBi _ ≤ _) _ hE

lemma coord_measurable_in_combined (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I))
    {F : Set HC}
    (hF : MeasurableSet[N_nil_I_borel n] F) :
    MeasurableSet[unSplitTri (ms_pre ×ₘ I_borel ×ₘ Inf_nil)] F :=
  (commute_with_add_dim ms_pre ▸ le_sup_left : N_nil_I_borel n ≤ _) _ hF

/-! ### Helper lemmas for the product factorization -/

/-- `N_nil_I_borel n` is the comap of `I_borel` through `(· n)`. -/
lemma N_nil_I_borel_eq_comap_coord (n : ℕ) :
    N_nil_I_borel n = (inferInstance : MeasurableSpace I).comap (· n : HC → I) := by
  simp only [N_nil_I_borel, unSplitTri, splitTri, MeasurableSpace.prod, N_nil,
    MeasurableSpace.comap_bot, MeasurableSpace.comap_comp, bot_sup_eq, sup_bot_eq]
  congr! 1

/-
If `unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel`, then `ms_pre ≤ pi`.
-/
lemma ms_pre_le_pi_of_le_Inf_borel (n : ℕ) (ms_pre : MeasurableSpace (Fin n → I))
    (h : unSplitBi (ms_pre ×ₘ Inf_nil) ≤ Inf_borel) :
    ms_pre ≤ (MeasurableSpace.pi : MeasurableSpace (Fin n → I)) := by
  contrapose! h
  simp_all +decide only [comap_le_iff_le_map, MeasurableEquiv.map_eq]
  intro H
  refine h ?_
  intro s hs
  convert H _ (MeasurableSet.prod hs MeasurableSet.univ) using 1
  constructor <;> intro h
  · exact MeasurableSet.prod h MeasurableSet.univ
  · convert h.preimage (f := fun x : Fin n → I => (x, fun _ : ℕ => (0 : I)))
      (measurable_id.prodMk measurable_const) using 1
    aesop

/-- `(splitBi n).symm ⁻¹' ((Prod.fst ∘ splitBi n) ⁻¹' A) = Prod.fst ⁻¹' A`. -/
lemma splitBi_symm_preimage_fst (n : ℕ) (A : Set (Fin n → I)) :
    (splitBi n).symm ⁻¹' ((Prod.fst ∘ splitBi n) ⁻¹' A) = Prod.fst ⁻¹' A := by
  rw [Set.preimage_comp]
  exact (splitBi n).symm_preimage_preimage _

/-- `(splitBi n).symm ⁻¹' ((· n) ⁻¹' B) = Prod.snd ⁻¹' ((· 0) ⁻¹' B)`. -/
lemma splitBi_symm_preimage_coord_n (n : ℕ) (B : Set I) :
    (splitBi n).symm ⁻¹' ((· n : HC → I) ⁻¹' B) =
    Prod.snd ⁻¹' ((· 0 : HC → I) ⁻¹' B) := by
  ext ⟨a, b⟩
  simp only [Set.mem_preimage]
  unfold splitBi MeasurableEquiv.sumPiEquivProdPi MeasurableEquiv.piCongrLeft
    MeasurableEquiv.trans Equiv.piCongrLeft
  simp +decide

/-- For the i.i.d. product measure, the k-th marginal equals `volume`. -/
lemma infinitePiNat_coord_marginal (k : ℕ) (B : Set I) (hB : MeasurableSet B) :
    Measure.infinitePiNat (fun _ => lebI) ((· k : HC → I) ⁻¹' B) =
    volume B := by
  have hk : k ∈ ({k} : Finset ℕ) := Finset.mem_singleton.mpr rfl
  have h_preimage :
      ((· k : HC → I) ⁻¹' B) =
        (({k} : Finset ℕ).restrict (π := fun _ => I)) ⁻¹' ((fun x => x ⟨k, hk⟩) ⁻¹' B) := rfl
  have h_pi :
      (fun x : ({k} : Finset ℕ) → I => x ⟨k, hk⟩) ⁻¹' B = Set.univ.pi (fun _ => B) := by
    ext x
    constructor
    · rintro h ⟨val, property⟩ -
      obtain rfl : val = k := Finset.mem_singleton.mp property
      exact h
    · intro h
      exact h ⟨k, hk⟩ (Set.mem_univ _)
  rw [h_preimage,
    ← Measure.map_apply (Finset.measurable_restrict _) (measurable_pi_apply _ hB),
    Measure.infinitePiNat_map_restrict, h_pi, Measure.pi_pi]
  simp

/-! ### The main factorization -/

/--
Core computation for `wp_unif_measure_product`, separated to avoid instance conflicts
with `ms_pre`. Here `A` and `B_I` are measurable in the standard (pi/Borel) instances.
-/
lemma wp_meas_measure_product_core
    (n : ℕ) (μ : @ProbabilityMeasure HC Inf_borel)
    {E F : Set HC} {A : Set (Fin n → I)} {B_I : Set I}
    (hA_pi : MeasurableSet A) (hB_I : MeasurableSet B_I)
    (hE_eq : E = (Prod.fst ∘ splitBi n) ⁻¹' A)
    (hF_eq : F = (· n : HC → I) ⁻¹' B_I) :
    ((μ.map (measurable_fst.comp (HC.splitBi n).measurable).aemeasurable |>.prod
      lebHC).map (HC.splitBi n).symm.measurable.aemeasurable).1 (E ∩ F) =
    μ.1 E * lebHC.toMeasure F := by
  subst hE_eq hF_eq
  change ((μ.toMeasure.map _).prod
      (Measure.infinitePiNat (fun _ => (volume : Measure I)))).map (splitBi n).symm
      ((Prod.fst ∘ ⇑(splitBi n) ⁻¹' A) ∩ ((fun x => x n) ⁻¹' B_I)) = _
  rw [Measure.map_apply (splitBi n).symm.measurable
        (hA_pi.preimage (by fun_prop) |>.inter (hB_I.preimage (by fun_prop))),
    show (splitBi n).symm ⁻¹' (Prod.fst ∘ ⇑(splitBi n) ⁻¹' A ∩ (fun x => x n) ⁻¹' B_I) =
      A ×ˢ ((fun x => x 0) ⁻¹' B_I) from by
      ext ⟨x, y⟩; simp [splitBi_symm_preimage_fst, splitBi_symm_preimage_coord_n],
    Measure.prod_prod,
    Measure.map_apply (by fun_prop) hA_pi,
    infinitePiNat_coord_marginal _ _ hB_I]
  change _ = μ.toMeasure _ * Measure.infinitePiNat (fun _ => (volume : Measure I)) _
  rw [infinitePiNat_coord_marginal _ _ hB_I]

end
