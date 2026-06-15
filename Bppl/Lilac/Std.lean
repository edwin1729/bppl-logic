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

def splitBi (n : ℕ) : (ℕ → I) ≃ᵐ (Fin n → I) × (ℕ → I) :=
  (MeasurableEquiv.piCongrLeft (fun _ => I) (finSumNatEquiv n)).symm.trans
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => I))

/-- Constructs a MeasurableSpace on a Hilbert cube given a MeasurableSpace on the first N
dimensions and another space on the rest of the infinite dimensions. -/
abbrev unSplitBi {n : ℕ} (ms : MeasurableSpace ((Fin n → I) × (ℕ → I))) : MeasurableSpace (ℕ → I) :=
  ms.comap (splitBi n)

def splitOne : (ℕ → I) ≃ᵐ I × (ℕ → I) :=
  (MeasurableEquiv.piCongrLeft (fun _ => I)
    (Equiv.natEquivNatSumPUnit.trans (Equiv.sumComm ℕ Unit))).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ => I)).trans
  ((MeasurableEquiv.funUnique Unit I).prodCongr (MeasurableEquiv.refl _)))

abbrev unSplitOne (ms : MeasurableSpace (I × (ℕ → I))) : MeasurableSpace (ℕ → I) :=
  ms.comap splitOne

def splitTri (n : ℕ) : (ℕ → I) ≃ᵐ (Fin n → I) × I × (ℕ → I) :=
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

lemma finite_footprint_of_ge {n n' : ℕ} {ms : MeasurableSpace (ℕ → I)} (hn : n ≤ n')
    (ff : FiniteFootprint n ms) : FiniteFootprint n' ms := by
  obtain ⟨ms_n, h_ms_n⟩ := ff
  use ms_n.comap (fun (a : Fin n' → I) (i : Fin n) => a (Fin.castLE hn i))
  convert h_ms_n using 1
  convert unSplitBi_eq_comap_fst n' _
  convert unSplitBi_eq_comap_fst n ms_n
  exact comap_comp

/-- `FiniteFootprint n ms` is equivalent to `ms` lying below the σ-algebra that only sees the
first `n` coordinates (where it carries the full σ-algebra `⊤`). This characterisation makes the
monotonicity and join-closure of `FiniteFootprint` immediate. -/
lemma finiteFootprint_iff_le {n : ℕ} {ms : MeasurableSpace (ℕ → I)} :
    FiniteFootprint n ms ↔ ms ≤ unSplitBi ((⊤ : MeasurableSpace (Fin n → I)) ×ₘ Inf_nil) := by
  rw [unSplitBi_eq_comap_fst]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ms', rfl⟩
    rw [unSplitBi_eq_comap_fst]
    exact MeasurableSpace.comap_mono le_top
  · refine ⟨MeasurableSpace.map (Prod.fst ∘ splitBi n) ms, ?_⟩
    rw [unSplitBi_eq_comap_fst]
    refine le_antisymm (fun s hs => ?_) comap_map_le
    obtain ⟨A, -, rfl⟩ := h s hs
    exact ⟨A, hs, rfl⟩

/-- `FiniteFootprint` is monotone: a smaller σ-algebra below one with footprint `n` also has
footprint `n`. -/
lemma ff_mono {n : ℕ} {ms₁ ms₂ : MeasurableSpace (ℕ → I)} (h : ms₂ ≤ ms₁)
    (ff : FiniteFootprint n ms₁) : FiniteFootprint n ms₂ :=
  finiteFootprint_iff_le.mpr (h.trans (finiteFootprint_iff_le.mp ff))

/-- `FiniteFootprint` is closed under joins. -/
lemma ff_sup {n : ℕ} {ms₁ ms₂ : MeasurableSpace (ℕ → I)}
    (ff₁ : FiniteFootprint n ms₁) (ff₂ : FiniteFootprint n ms₂) :
    FiniteFootprint n (ms₁ ⊔ ms₂) :=
  finiteFootprint_iff_le.mpr
    (sup_le (finiteFootprint_iff_le.mp ff₁) (finiteFootprint_iff_le.mp ff₂))

lemma commute (le_α : msα₁ ≤ msα₂) (le_β : msβ₁ ≤ msβ₂) :
    (MeasurableSpace.prod msα₁ msβ₂) ⊔ (MeasurableSpace.prod msα₂ msβ₁) =
    MeasurableSpace.prod msα₂ msβ₂ := by
  unfold MeasurableSpace.prod
  rw [sup_sup_sup_comm,
      sup_eq_right.mpr (MeasurableSpace.comap_mono le_α),
      sup_eq_left.mpr (MeasurableSpace.comap_mono le_β)]

private lemma commute_over_tri {N : ℕ} (N_ms : MeasurableSpace (Fin N → I)) :
    unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil) ⊔ unSplitTri (N_ms ×ₘ I_nil ×ₘ Inf_nil)
    = unSplitTri (N_ms ×ₘ I_borel ×ₘ Inf_nil) := by
  have le_β : I_nil ×ₘ Inf_nil ≤ I_borel ×ₘ Inf_nil := sup_le_sup_right (comap_mono bot_le) _
  rw [← comap_sup, commute bot_le le_β]

private lemma eq_N_ms {N : ℕ} (N_ms : MeasurableSpace (Fin N → I))
    : unSplitBi (N_ms ×ₘ Inf_nil) = unSplitTri (N_ms ×ₘ I_nil ×ₘ Inf_nil) := by
  simp only [prod, comap_bot, bot_le, sup_of_le_left, comap_comp, le_refl]
  congr 1

/-- Used in the construction for wp_meas, where a single dimension gets added between at the
separation index separatiing the finite part with interesting MeasureSpace and the infinite part
with boring MeasurableSpace. -/
lemma commute_with_add_dim {N : ℕ} (N_ms : MeasurableSpace (Fin N → I))
    : unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil) ⊔ unSplitBi (N_ms ×ₘ Inf_nil)
      = unSplitTri (N_ms ×ₘ I_borel ×ₘ Inf_nil) := by
  rw [eq_N_ms N_ms]
  exact commute_over_tri N_ms

abbrev N_nil_I_borel (N : ℕ) := unSplitTri ((N_nil N) ×ₘ I_borel ×ₘ Inf_nil)
abbrev N_borel_I_borel (N : ℕ) := unSplitTri ((N_borel N) ×ₘ I_borel ×ₘ Inf_nil)

/-- this helper relates `unSplitTri` at `N` to `unSplitBi` at `N+1` by absorbing the middle
`I`-coordinate into the finite (first) part. -/
lemma unSplitTri_eq_unSplitBi_succ {N : ℕ}
    (ms_N : MeasurableSpace (Fin N → I))
    (ms_I : MeasurableSpace I) :
    unSplitTri (ms_N ×ₘ ms_I ×ₘ Inf_nil) =
    @unSplitBi (N + 1)
      ((MeasurableSpace.comap (· ∘ Fin.castSucc) ms_N ⊔
        MeasurableSpace.comap
          (fun f => f (Fin.last N)) ms_I) ×ₘ
        Inf_nil) := by
          simp +decide only [unSplitTri, prod, comap_bot, bot_le, sup_of_le_left, comap_comp,
            comap_sup, unSplitBi];
          congr! 2

/-- `FiniteFootprint` for an arbitrary sub-σ-algebra on the first `N` coordinates
combined with `I_borel` on coordinate `N`. -/
lemma ff_unSplitTri_I_borel {n : ℕ} (ms : MeasurableSpace (Fin n → I)) :
    ∃ n', FiniteFootprint n' (unSplitTri (ms ×ₘ I_borel ×ₘ Inf_nil)) :=
  ⟨n + 1, _, unSplitTri_eq_unSplitBi_succ ms I_borel⟩

lemma ff_N_nil_I_borel {N : ℕ} : ∃ n, FiniteFootprint n (N_nil_I_borel N) :=
  ff_unSplitTri_I_borel (N_nil N)
lemma ff_N_borel_I_borel {N : ℕ} : ∃ n, FiniteFootprint n (N_borel_I_borel N) :=
  ff_unSplitTri_I_borel (N_borel N)

lemma N_nil_I_borel_le_Inf_borel (N : ℕ) : N_nil_I_borel N ≤ Inf_borel := by
  refine MeasurableSpace.comap_le_iff_le_map.mpr ?_
  simp only [prod, comap_bot, bot_le, sup_of_le_left, comap_comp, sup_of_le_right,
    MeasurableSpace.map, MeasurableEquiv.measurableSet_preimage]
  exact MeasurableSpace.comap_le_iff_le_map.mpr (measurable_snd.fst)

lemma N_borel_I_borel_le_Inf_borel (N : ℕ) : N_borel_I_borel N ≤ Inf_borel := by
  unfold N_borel_I_borel
  simp only [prod, N_borel, Inf_nil, comap_bot, bot_le, sup_of_le_left, comap_comp,
    comap_sup, sup_le_iff]
  constructor <;> intro s hs <;>
    rcases hs with ⟨t, ht, rfl⟩
  · exact measurable_pi_lambda _
      (fun _ => measurable_pi_apply _) ht
  · apply_rules [MeasurableSet.preimage, ht]
    fun_prop

/-- The combined σ-algebra on first `N` coords + Borel on coord `N` is ≤ `Inf_borel`. -/
lemma unSplitTri_I_borel_le_Inf_borel {N : ℕ} (ms : MeasurableSpace (Fin N → I))
    (hms : ms ≤ N_borel N) : unSplitTri (ms ×ₘ I_borel ×ₘ Inf_nil) ≤ Inf_borel := by
  refine trans ?_ ( N_borel_I_borel_le_Inf_borel N )
  apply_rules [ MeasurableSpace.comap_mono, sup_le_sup_right ]

@[fun_prop]
lemma coordProj_measurable (n : ℕ) :
    @Measurable (ℕ → I) I (N_nil_I_borel n) _ (fun ω ↦ ω n) :=
  (Measurable.comp (measurable_snd.fst)) (comap_measurable _)


/-- The first component of `splitBi n ω` at index `i : Fin n` equals `ω ↑i`. -/
@[simp]
lemma splitBi_fst_apply (n : ℕ) (ω : ℕ → I) (i : Fin n) : (splitBi n ω).1 i = ω i := rfl
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
noncomputable def unif01_sem : Measure ℝ :=
  Measure.map Subtype.val (MeasureSpace.volume (α := Set.Icc (0 : ℝ) 1))

instance : IsProbabilityMeasure unif01_sem :=
  isProbabilityMeasure_map measurable_subtype_coe.aemeasurable


-- this should be refactored into a type class, or use the `fun_prop` style, where
-- lemmas constructing the `ff` property are annotated with `fun_prop`
/-- A measurable function from `HC` with finite footprint. -/
structure RV (β : Type*) [msβ : MeasurableSpace β] extends @MeasurableFun HC β MeasurableSpace.pi _
    where
  /-- Finite footprint -/
  ff : ∃ n, HC.FiniteFootprint n (msβ.comap toFun)

namespace RV

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

instance instFunLikeRV : FunLike (RV β) HC β where
  coe D := D.toFun
  coe_injective' f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h

instance instCoeRV : Coe (RV β) (HC -m→ β) where
  coe D := D.toMeasurableFun

instance : Mul (RV ℝ) where
  mul M N := ⟨⟨λ ω ↦ M ω * N ω, M.meas.mul N.meas⟩, by
    obtain ⟨n₁, h₁⟩ := M.ff
    obtain ⟨n₂, h₂⟩ := N.ff
    refine ⟨max n₁ n₂, HC.ff_mono (Measurable.comap_le ?_)
      (HC.ff_sup (HC.finite_footprint_of_ge (le_max_left n₁ n₂) h₁)
        (HC.finite_footprint_of_ge (le_max_right n₁ n₂) h₂))⟩
    exact (Measurable.of_comap_le le_sup_left).mul (Measurable.of_comap_le le_sup_right)⟩

-- abbrev mul (M N : RV ℝ) : RV ℝ := ⟨⟨λ ω ↦ M ω * N ω, sorry⟩, sorry⟩

abbrev ite (E : RV Bool) (M N : RV α) : RV α :=
  ⟨⟨λ ω ↦ if E ω then M ω else N ω,
      Measurable.ite (E.meas (measurableSet_singleton true)) M.meas N.meas⟩, by
    obtain ⟨nE, hE⟩ := E.ff
    obtain ⟨nM, hM⟩ := M.ff
    obtain ⟨nN, hN⟩ := N.ff
    refine ⟨max (max nE nM) nN, HC.ff_mono (Measurable.comap_le ?_)
      (HC.ff_sup (HC.ff_sup
        (HC.finite_footprint_of_ge ((le_max_left nE nM).trans (le_max_left _ nN)) hE)
        (HC.finite_footprint_of_ge ((le_max_right nE nM).trans (le_max_left _ nN)) hM))
        (HC.finite_footprint_of_ge (le_max_right _ nN) hN))⟩
    exact Measurable.ite
      ((Measurable.of_comap_le (le_sup_left.trans le_sup_left)) (measurableSet_singleton true))
      (Measurable.of_comap_le (le_sup_right.trans le_sup_left))
      (Measurable.of_comap_le le_sup_right)⟩

abbrev prod [MeasurableSpace α] [MeasurableSpace β]
    (f : RV α) (g : RV β) : RV (α × β) :=
  ⟨⟨fun (r : HC) ↦ ((f r : α), (g r : β)), Measurable.prod f.meas g.meas⟩, by
    obtain ⟨n₁, h₁⟩ := f.ff
    obtain ⟨n₂, h₂⟩ := g.ff
    refine ⟨max n₁ n₂, HC.ff_mono (Measurable.comap_le ?_)
      (HC.ff_sup (HC.finite_footprint_of_ge (le_max_left n₁ n₂) h₁)
        (HC.finite_footprint_of_ge (le_max_right n₁ n₂) h₂))⟩
    exact (Measurable.of_comap_le le_sup_left).prod (Measurable.of_comap_le le_sup_right)
  ⟩
notation x " ;; " xs => RV.prod x xs

abbrev comp [MeasurableSpace β] [MeasurableSpace γ] (g : β -m→ γ) (f : RV β) : RV γ :=
  ⟨⟨g ∘ f, Measurable.comp g.meas f.meas⟩, by
    obtain ⟨n, hn⟩ := f.ff
    refine ⟨n, HC.ff_mono ?_ hn⟩
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono g.meas.comap_le⟩
notation g " ∘ᵣ " f => RV.comp g f

def coordProj (n : ℕ) : RV I := ⟨⟨fun ω ↦ ω n, by fun_prop⟩, by
  obtain ⟨m, hm⟩ := HC.ff_N_nil_I_borel (N := n)
  exact ⟨m, HC.ff_mono (measurable_iff_comap_le.mp (HC.coordProj_measurable n)) hm⟩⟩

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
