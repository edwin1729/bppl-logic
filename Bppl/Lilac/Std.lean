/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit true

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
def FiniteFootprint (ms : MeasurableSpace (ℕ → I)) : Prop :=
  ∃ n : ℕ, ∃ ms' : MeasurableSpace (Fin n → I), ms = unSplitBi (ms' ×ₘ Inf_nil)

end
end HC
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

structure MeasurableFun (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- underlying function -/
  toFun : α → β
  meas: Measurable toFun

notation α " -m→ " β => MeasurableFun α β

abbrev measurableFun_fst : (α × β) -m→ α := ⟨_ , measurable_fst⟩

abbrev measurableFun_snd : (α × β) -m→ β := ⟨_ , measurable_snd⟩

abbrev MeasurableFun.fst (f : α -m→ β × γ) : α -m→ β := ⟨_ , Measurable.fst f.2⟩

abbrev MeasurableFun.snd (f : α -m→ β × γ) : α -m→ γ := ⟨_ , Measurable.snd f.2⟩

instance instCoeMeasurableFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    : CoeFun (α -m→ β) (fun _ => α → β) where
  coe f := f.toFun

abbrev HC := ℕ → Set.Icc (0:ℝ) 1

instance : Inhabited HC where
  default := fun _ ↦ 0

structure RV (β : Type*) [msβ : MeasurableSpace β] extends MeasurableFun HC β where
  /-- Finite footprint -/
  ff : HC.FiniteFootprint (msβ.comap toFun)

instance instCoeFunRV {β : Type*} [MeasurableSpace β] : CoeFun (RV β) (fun _ => HC → β) where
  coe D := D.toFun

instance instCoeRV {β : Type*} [MeasurableSpace β] : Coe (RV β) (HC -m→ β) where
  coe D := D.toMeasurableFun

abbrev RV.prod [MeasurableSpace α] [MeasurableSpace β]
    (f : RV α) (g : RV β) : RV (α × β) :=
  ⟨⟨fun (r : HC) ↦ ((f r : α), (g r : β)), Measurable.prod f.meas g.meas⟩, by
    obtain ⟨n₁, h₁⟩ := f.ff
    obtain ⟨n₂, h₂⟩ := g.ff
    use max n₁ n₂
    simp only
    sorry
  ⟩
notation x " ;; " xs => RV.prod x xs

def RV.comp [MeasurableSpace β] [MeasurableSpace γ] (g : β -m→ γ) (f : RV β) : RV γ :=
  ⟨⟨g ∘ f, Measurable.comp g.meas f.meas⟩, sorry⟩
notation g " ∘ᵣ " f => RV.comp g f

abbrev fProd {α β γ : Type*} (f : α → β) (g : α → γ) (x : α) : β × γ := (f x, g x)
notation " ⟨ " f ", " g " ⟩ᶠ " => fProd f g

namespace MeasurableFunc
variable {α β γ : Type*} [MeasurableSpace α]


end MeasurableFunc
