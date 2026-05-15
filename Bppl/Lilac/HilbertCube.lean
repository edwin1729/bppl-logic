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

/-- The σ-algebra is only "interesting" in the first `n` coordinates for some finite `n`.
In the rest of the coordinates, its the `univ` set. -/
def FiniteFootprint (ms : MeasurableSpace (ℕ → I)) : Prop :=
  ∃ n : ℕ, ∃ ms' : MeasurableSpace (Fin n → I), ms = unSplitBi (ms' ×ₘ Inf_nil)
  -- ∀ F : Set HC, MeasurableSet[ms] F →
  --   ∃ F' : Set (Fin n → Set.Icc (0:ℝ) 1),
  --     F = HC.splitMeasEquiv n ⁻¹' (F' ×ˢ (@Set.univ HC))

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
abbrev N_nil_I_borel (N : ℕ) := unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil)
abbrev N_borel_I_borel (N : ℕ) := unSplitTri ((N_borel N) ×ₘ I_borel ×ₘ Inf_nil)

/-
this helper relates `unSplitTri` at `N` to `unSplitBi`
at `N+1` by absorbing the middle `I`-coordinate into the
finite (first) part.
-/
lemma unSplitTri_eq_unSplitBi_succ {N : ℕ}
    (ms_N : MeasurableSpace (Fin N → I))
    (ms_I : MeasurableSpace I) :
    unSplitTri (ms_N ×ₘ ms_I ×ₘ Inf_nil) =
    @unSplitBi (N + 1)
      ((MeasurableSpace.comap (· ∘ Fin.castSucc) ms_N ⊔
        MeasurableSpace.comap
          (fun f => f (Fin.last N)) ms_I) ×ₘ
        Inf_nil) := by
          simp +decide [ unSplitTri, unSplitBi, MeasurableSpace.prod ];
          congr! 2


/-- `FiniteFootprint` for an arbitrary sub-σ-algebra on the first `N` coordinates
combined with `I_borel` on coordinate `N`. -/
lemma ff_unSplitTri_I_borel {N : ℕ} (ms : MeasurableSpace (Fin N → I)) :
    FiniteFootprint (unSplitTri (ms ×ₘ I_borel ×ₘ Inf_nil)) :=
  ⟨N + 1, _, unSplitTri_eq_unSplitBi_succ ms I_borel⟩

lemma ff_N_nil_I_borel {N : ℕ} : FiniteFootprint (N_nil_I_borel N) :=
  ff_unSplitTri_I_borel (N_nil N)
lemma ff_N_borel_I_borel {N : ℕ} : FiniteFootprint (N_borel_I_borel N) :=
  ff_unSplitTri_I_borel (N_borel N)

lemma N_nil_I_borel_le_Inf_borel (N : ℕ) : N_nil_I_borel N ≤ Inf_borel := by
  unfold N_nil_I_borel
  refine' MeasurableSpace.comap_le_iff_le_map.mpr _
  simp +decide [MeasurableSpace.prod,
    MeasurableSpace.map]
  exact MeasurableSpace.comap_le_iff_le_map.mpr
    (measurable_snd.fst)

lemma N_borel_I_borel_le_Inf_borel (N : ℕ) : N_borel_I_borel N ≤ Inf_borel := by
  unfold N_borel_I_borel
  simp +decide [N_borel, Inf_nil,
    MeasurableSpace.prod]
  constructor <;> intro s hs <;>
    rcases hs with ⟨t, ht, rfl⟩
  · exact measurable_pi_lambda _
      (fun _ => measurable_pi_apply _) ht
  · apply_rules [MeasurableSet.preimage, ht]
    fun_prop

/-- The combined σ-algebra on first `N` coords + Borel on coord `N` is ≤ `Inf_borel`. -/
lemma unSplitTri_I_borel_le_Inf_borel {N : ℕ}
    (ms : MeasurableSpace (Fin N → I))
    (hms : ms ≤ N_borel N) :
    unSplitTri (ms ×ₘ I_borel ×ₘ Inf_nil) ≤
      Inf_borel := by
        refine' trans _ ( N_borel_I_borel_le_Inf_borel N );
        apply_rules [ MeasurableSpace.comap_mono, sup_le_sup_right ]
/-
The second-first component of `splitTri n ω` equals `ω n`, the `n`-th coordinate.
-/
lemma splitTri_snd_fst (n : ℕ) (ω : ℕ → I) : (splitTri n ω).2.1 = ω n := by
  unfold splitTri; aesop;
/-
The `n`-th coordinate projection `fun ω ↦ ↑(ω n) : HC → ℝ` is measurable
    with respect to `N_nil_I_borel n`, since this σ-algebra includes `I_borel`
    on coordinate `n`.
-/
lemma coordProj_measurable (n : ℕ) :
    @Measurable (ℕ → I) ℝ (N_nil_I_borel n) _ (fun ω ↦ (↑(ω n) : ℝ)) :=
  (Measurable.comp (Measurable.subtype_val measurable_snd.fst)) (comap_measurable _)


end

/-- The first component of `splitBi n ω` at index `i : Fin n` equals `ω ↑i`. -/
@[simp]
lemma splitBi_fst_apply (n : ℕ) (ω : ℕ → I) (i : Fin n) : (splitBi n ω).1 i = ω i := rfl

end HC
