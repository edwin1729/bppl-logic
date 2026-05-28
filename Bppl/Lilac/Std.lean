/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProductMeasure

/-! # Collection of Defintions used throughout the project
-/

namespace HC
open unitInterval MeasurableSpace
noncomputable section

variable {α β : Type*} {msα₁ msα₂ : MeasurableSpace α} {msβ₁ msβ₂ : MeasurableSpace β}
-- scoped[HilbertCube] infixr:25 " ×ₘ " => MeasurableSpace.prod
scoped infixr:60 " ×ₘ " => MeasurableSpace.prod

-- standard borel measurable spaces
abbrev Inf_borel : MeasurableSpace (ℕ → I) := inferInstance
abbrev N_borel (N : ℕ) : MeasurableSpace (Fin N → I) := inferInstance
-- the measurabe space with only univ and empty
abbrev Inf_nil : MeasurableSpace (ℕ → I) := ⊥
abbrev N_nil (N : ℕ) : MeasurableSpace (Fin N → I) := ⊥
abbrev I_nil : MeasurableSpace I := ⊥
abbrev I_borel : MeasurableSpace I := inferInstance

noncomputable def splitBi (n : ℕ) : (ℕ → I) ≃ᵐ (Fin n → I) × (ℕ → I) :=
  (MeasurableEquiv.piCongrLeft (fun _ => I) (finSumNatEquiv n)).symm.trans
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => I))

/-- Constructs a MeasurableSpace on a Hilbert cube given a MeasurableSpace on the first N
dimensions and another space on the rest of the infinite dimensions. -/
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

/-- The σ-algebra is only "interesting" in the first `n` coordinates for some finite `n`.
In the rest of the coordinates, its the `univ` set. -/
def FiniteFootprint (n : ℕ) (ms : MeasurableSpace (ℕ → I)) : Prop :=
  ∃ ms' : MeasurableSpace (Fin n → I), ms = unSplitBi (ms' ×ₘ Inf_nil)

/-- `unSplitBi (ms_pre ×ₘ Inf_nil)` is the comap of `ms_pre` through `fst ∘ splitBi n`. -/
lemma unSplitBi_eq_comap_fst (n : ℕ)
    (ms_pre : MeasurableSpace (Fin n → I)) :
    unSplitBi (ms_pre ×ₘ Inf_nil) = ms_pre.comap (Prod.fst ∘ splitBi n) := by
  simp only [unSplitBi, Inf_nil, MeasurableSpace.prod, MeasurableSpace.comap_bot,
    sup_bot_eq, MeasurableSpace.comap_comp]

lemma finite_footprint_of_ge {n n' : ℕ} {ms : MeasurableSpace (ℕ → I)} (hn : n ≤ n') (ff : FiniteFootprint n ms)
    : FiniteFootprint n' ms := by
  obtain ⟨ms_n, h_ms_n⟩ := ff
  use ms_n.comap (fun (a : Fin n' → I) (i : Fin n) => a (Fin.castLE hn i))
  convert h_ms_n using 1
  convert unSplitBi_eq_comap_fst n' _
  convert unSplitBi_eq_comap_fst n ms_n
  ext; simp [splitBi]

end
end HC

open MeasureTheory MeasureTheory.Measure unitInterval
open ProbabilityTheory (Kernel)
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

structure MeasurableFun (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- underlying function -/
  toFun : α → β
  meas: Measurable toFun

@[fun_prop]
lemma measurable_MeasurableFun (f : MeasurableFun α β) : Measurable f.toFun := f.meas

notation α " -m→ " β => MeasurableFun α β

abbrev measurableFun_fst : (α × β) -m→ α := ⟨_ , measurable_fst⟩

abbrev measurableFun_snd : (α × β) -m→ β := ⟨_ , measurable_snd⟩

abbrev MeasurableFun.fst (f : α -m→ β × γ) : α -m→ β := ⟨_ , Measurable.fst f.2⟩

abbrev MeasurableFun.snd (f : α -m→ β × γ) : α -m→ γ := ⟨_ , Measurable.snd f.2⟩

instance instFunLikeMeasurableFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    : FunLike (α -m→ β) α β where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

abbrev HC := ℕ → Set.Icc (0:ℝ) 1

instance : Inhabited HC where
  default := fun _ ↦ 0

/-- The Lebesgue measure on the Hilbert cube: the infinite product of uniform measures
on the unit interval. -/
noncomputable abbrev lebHC : @ProbabilityMeasure HC HC.Inf_borel :=
  ⟨Measure.infinitePiNat (fun _ => (MeasureTheory.volume : Measure unitInterval)),
   inferInstance⟩

noncomputable abbrev lebI : Measure I := volume

/-- The semantic (native lean) uniform distribution in the interval [0,1].
This is the pushforward of Lebesgue measure on `I = Set.Icc 0 1`
via the subtype coercion `↑ : I → ℝ`. -/
noncomputable def lebI' : Measure ℝ :=
  Measure.map Subtype.val (MeasureSpace.volume (α := Set.Icc (0 : ℝ) 1))

instance : IsProbabilityMeasure lebI' :=
  isProbabilityMeasure_map measurable_subtype_coe.aemeasurable


-- this should be refactored into a type class, or use the `fun_prop` style, where
-- lemmas constructing the `ff` property are annotated with `fun_prop`
/-- A measurable function from `HC` with finite footprint. -/
structure RV (β : Type*) [msβ : MeasurableSpace β] extends @MeasurableFun HC β MeasurableSpace.pi _ where
  /-- Finite footprint -/
  ff : ∃ n, HC.FiniteFootprint n (msβ.comap toFun)

namespace RV

instance instFunLikeRV {β : Type*} [MeasurableSpace β] : FunLike (RV β) HC β where
  coe D := D.toFun
  coe_injective' f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h

instance instCoeRV {β : Type*} [MeasurableSpace β] : Coe (RV β) (HC -m→ β) where
  coe D := D.toMeasurableFun

abbrev prod [MeasurableSpace α] [MeasurableSpace β]
    (f : RV α) (g : RV β) : RV (α × β) :=
  ⟨⟨fun (r : HC) ↦ ((f r : α), (g r : β)), Measurable.prod f.meas g.meas⟩, by
    obtain ⟨n₁, h₁⟩ := f.ff
    obtain ⟨n₂, h₂⟩ := g.ff
    use max n₁ n₂
    simp only
    sorry
  ⟩
notation x " ;; " xs => RV.prod x xs

abbrev comp [MeasurableSpace β] [MeasurableSpace γ] (g : β -m→ γ) (f : RV β) : RV γ :=
  ⟨⟨g ∘ f, Measurable.comp g.meas f.meas⟩, sorry⟩
notation g " ∘ᵣ " f => RV.comp g f

abbrev fProd {α β γ : Type*} (f : α → β) (g : α → γ) (x : α) : β × γ := (f x, g x)
notation " ⟨ " f ", " g " ⟩ᶠ " => fProd f g

-- instance foo : Unique (Fin 0 → φ) := inferInstance

abbrev ff_const [msβ : MeasurableSpace β] (constVal : β)
    : ∃ n, HC.FiniteFootprint n (msβ.comap (λ _a : HC ↦ constVal)) := by
  use 0, ⊥
  rw [MeasurableSpace.comap_const]
  unfold HC.unSplitBi
  rw [MeasurableSpace.comap_prodMk]
  simp

/-- The constant function is an RV. This is useful for representing the dentotation
of programs like `unif01` or `flip` where the `constVal` is the advertised measure,
and the ignored parameters are the random variable context. -/
abbrev const (constVal : β) [MeasurableSpace β] : RV β :=
  ⟨⟨λ _a : HC ↦ constVal, measurable_const⟩, ff_const constVal⟩

end RV
