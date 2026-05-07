import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.UnitInterval

namespace HC
-- equivalence of generated-σ-algebras

open unitInterval MeasurableSpace
noncomputable section

variable {α β : Type*} {msα₁ msα₂ : MeasurableSpace α} {msβ₁ msβ₂ : MeasurableSpace β}

lemma commute (le_α : msα₁ ≤ msα₂) (le_β : msβ₁ ≤ msβ₂) :
    (MeasurableSpace.prod msα₁ msβ₂) ⊔ (MeasurableSpace.prod msα₂ msβ₁) =
    MeasurableSpace.prod msα₂ msβ₂ := by
  unfold MeasurableSpace.prod
  rw [sup_sup_sup_comm,
      sup_eq_right.mpr (MeasurableSpace.comap_mono le_α),
      sup_eq_left.mpr (MeasurableSpace.comap_mono le_β)]

-- notation:25 α " ≃ᵐ[ " msα " , " msβ  " ] " β => @MeasurableEquiv α β msα msβ

-- scoped[HilbertCube] infixr:25 " ×ₘ " => MeasurableSpace.prod
scoped infixr:60 " ×ₘ " => MeasurableSpace.prod

noncomputable def splitBi (n : ℕ) : (ℕ → I) ≃ᵐ (Fin n → I) × (ℕ → I) :=
  (MeasurableEquiv.piCongrLeft (fun _ => I) (finSumNatEquiv n)).symm.trans
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => I))

abbrev unSplitBi {n : ℕ} (ms : MeasurableSpace ((Fin n → I) × (ℕ → I))) : MeasurableSpace (ℕ → I) :=
  ms.comap (splitBi n)

noncomputable def splitOne : (ℕ → I) ≃ᵐ I × (ℕ → I) :=
  (MeasurableEquiv.piCongrLeft (fun _ => I)
    (Equiv.natEquivNatSumPUnit.trans (Equiv.sumComm ℕ Unit))).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ => I)).trans
  ((MeasurableEquiv.funUnique Unit I).prodCongr (MeasurableEquiv.refl _)))

abbrev unSplitOne (ms : MeasurableSpace (I × (ℕ → I))) : MeasurableSpace (ℕ → I) :=
  ms.comap splitOne

noncomputable def splitTri (n : ℕ) : (ℕ → I) ≃ᵐ (Fin n → I) × I × (ℕ → I) :=
  (splitBi n).trans ((MeasurableEquiv.refl _).prodCongr splitOne)

abbrev unSplitTri {n : ℕ} (ms : MeasurableSpace ((Fin n → I) × I × (ℕ → I)))
    : MeasurableSpace (ℕ → I) :=
  ms.comap (splitTri n)

-- noncomputable def split (n : ℕ) (ms₂ : MeasurableSpace ((Fin n → I) × (ℕ → I))) :
--     (ℕ → I) ≃ᵐ[ms₂.comap (splitEquiv n), ms₂] ((Fin n → I) × (ℕ → I)) where
--   toEquiv := (splitEquiv n).toEquiv
--   measurable_toFun := comap_measurable _
--   measurable_invFun := Measurable.of_comap_le (by
--     rw [comap_comp, show (splitEquiv n : (ℕ → I) → _) ∘ (splitEquiv n).symm = id from
--       funext (splitEquiv n).apply_symm_apply, comap_id])

-- standard borel measurable spaces
abbrev Inf_borel : MeasurableSpace (ℕ → I) := inferInstance
abbrev N_borel (N : ℕ) : MeasurableSpace (Fin N → I) := inferInstance
-- the measurabe space with only univ and empty
abbrev Inf_nil : MeasurableSpace (ℕ → I) := ⊥
abbrev N_nil (N : ℕ) : MeasurableSpace (Fin N → I) := ⊥
abbrev I_nil : MeasurableSpace I := ⊥
abbrev I_borel : MeasurableSpace I := inferInstance

-- now we look at some lemmas of the shape we want. Specifically
-- (borel, nil, nil) ⊔ (nil, borel, nil) = (borel, borel, nil)

lemma commute_over_equiv3 {N : ℕ} (N_ms : MeasurableSpace (Fin N → I))
    : unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil) ⊔ unSplitTri (N_ms ×ₘ I_nil ×ₘ Inf_nil) = unSplitTri (N_ms ×ₘ I_borel ×ₘ Inf_nil) := by
  have le_β : I_nil ×ₘ Inf_nil ≤ I_borel ×ₘ Inf_nil := sup_le_sup_right (comap_mono bot_le) _
  rw [← comap_sup, commute bot_le le_β]

lemma eq_N_ms {N : ℕ} (N_ms : MeasurableSpace (Fin N → I))
    : unSplitBi (N_ms ×ₘ Inf_nil) = unSplitTri (N_ms ×ₘ I_nil ×ₘ Inf_nil) := by
  simp only [prod, comap_bot, bot_le, sup_of_le_left, comap_comp, le_refl]
  congr 1

lemma commute_over_equiv4 {N : ℕ} (N_ms : MeasurableSpace (Fin N → I))
    : unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil) ⊔ unSplitBi (N_ms ×ₘ Inf_nil)
      = unSplitTri (N_ms ×ₘ I_borel ×ₘ Inf_nil) := by
  rw [eq_N_ms N_ms]
  exact commute_over_equiv3 N_ms
-- it looks like Mathlib has a pain point with being explicitly parametric over the measurable space.
-- what we will do for this instead is to deal with this by hoping that any one point the inferred
-- type is unambiguous? Lets see....

end
end HC
