import Iris.BI.BIBase
import Mathlib.Data.PFun
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


/- Instantiating the Kripke Resource Monoid according to  Lilac -/

open MeasureTheory MeasurableSpace
section KRM
-- set_option quotPrecheck false
/-- Partial Commutative Monoid -/
class PCM (α : Type*) extends One α where
  binop : α → α →. α -- partial binary operation

notation a:arg " • " b:arg => PCM.binop a b

class PCM' (α : Type*) extends PCM α where
  one_mul : ∀ a : α, binop 1 a = a
  mul_one : ∀ a : α, binop a 1 = a
  comm : ∀ a b, binop a b = binop b a
  assoc : ∀ a b c : α,
    (binop a b) >>= (fun ab => (binop ab c)) =
    (binop b c) >>= (fun bc => (binop a bc))

class KRM (α : Type*) extends PCM α, PartialOrder α where
  ge_mul_mono : ∀ x x' y y' p' : α,
    x ≤ x' → y ≤ y' →
    (x' • y' = some p') → ∃ p, (x • y = some p) ∧  p ≤ p'

-- Now we want to instantiate this with a probability space
-- We need a type of probability spaces parametrized by given carrier type α

def ProbabilitySpace (α : Type*) := Σ (m: MeasurableSpace α), @ProbabilityMeasure α m

namespace ProbabilitySpace

variable {α : Type*} {m m0 : MeasurableSpace α}

-- to mathlib?
-- maybe I should use `Measure.trim` instead of copying and adapting its definition
noncomputable
def trim
  (μ : @ProbabilityMeasure α m0) (hm : m ≤ m0) : @ProbabilityMeasure α m :=
    ⟨Measure.trim μ hm,
      ⟨by
        have eq_univ : μ Set.univ = Measure.trim μ hm Set.univ := by
          simp only [ProbabilityMeasure.coeFn_univ, ENNReal.coe_one, MeasurableSet.univ,
            toMeasure_apply, Measure.coe_toOuterMeasure, measure_univ, Measure.trim]
        simp_all only [ProbabilityMeasure.coeFn_univ, ENNReal.coe_one, Measure.trim]
    ⟩⟩

-- why is μ.trim syntax not working?
lemma trim_measurableSet_eq {s : Set α} {μ : @ProbabilityMeasure α m0}
  (hm : m ≤ m0) (hs : @MeasurableSet α m s) : trim μ hm s = μ s := by
    have foo := @MeasureTheory.trim_measurableSet_eq _ _ _ μ.1 _ hm hs
    rw [trim]
    simp_all only [ProbabilityMeasure.val_eq_to_measure, ProbabilityMeasure.mk_apply]
    rfl

end ProbabilitySpace

open Classical

-- The relevant lemma for explicitly stating what `⊥` is, is `measurableSet_bot_iff`
noncomputable instance instOne {α : Type*} [nonempty : Nonempty α] : One (ProbabilitySpace α) where
  one := ⟨⊥, ⟨@Measure.ofMeasurable α ⊥ (fun s hs ↦ if s = ∅ then 0 else 1) (by simp) sorry,
      -- prove that the measure is a probability measure, μ univ = 1
      ⟨by
        rw [@Measure.ofMeasurable_apply α ⊥]
        · simp
        · exact MeasurableSet.univ
      ⟩⟩
  ⟩

section indep_comb

variable {α : Type*} (ℰ ℱ 𝒢 𝒢': ProbabilitySpace α)

-- At the moment I talk explicitly about properties of combinations of measures
-- (uniqueness/existence). These are trivial for spaces. However it may be cleaner later on
-- to talk of the space as a whole instead

-- TODO fix the need to do `toMeasurableSpace`. It's annoying
-- notation "∀ " s:arg " ∈ᵐ " P:arg ", " body:arg => ∀ s, MeasurableSet[P] s → body

-- why does the R.volume part work? I think the `measure` is a garbage value for sets which
-- are not measurable. But of course this is fine (cause the prop would just be false in
-- garbage value case)
def indep_comb_measure (ρ : @ProbabilityMeasure α (ℰ.1 ⊔ ℱ.1)) :=
    ∀ E F : Set α, MeasurableSet[ℰ.1] E → MeasurableSet[ℱ.1] F →
      ρ (E ∩ F) = ℰ.2 E * ℱ.2 F

-- The problem with the above is that it forces the measurablespace to be `ℰ.1 ⊔ ℱ.1`
-- We don't want that.
def indep_comb_measure' (𝒢 : ProbabilitySpace α) (ρ : @ProbabilityMeasure α (ℰ.1 ⊔ ℱ.1)) :=
    𝒢.1 = (ℰ.1 ⊔ ℱ.1) ∧
    ∀ E F : Set α, MeasurableSet[ℰ.1] E → MeasurableSet[ℱ.1] F →
      ρ (E ∩ F) = ℰ.2 E * ℱ.2 F

def existence_cond : Prop := ∃ ρ, indep_comb_measure ℰ ℱ ρ

def indep_comb : Prop := ∃ (h : ℰ.1 ⊔ ℱ.1 = 𝒢.1),
  indep_comb_measure ℰ ℱ (ProbabilitySpace.trim 𝒢.2 (le_of_eq h))

-- What I want to do is t

-- Lemma 2.3 (independent combinations are unique)
-- use the π-λ-theorem here
lemma uniqueness_indep_comb (h₁ : indep_comb ℰ ℱ 𝒢) (h₂ : indep_comb ℰ ℱ 𝒢') : 𝒢 = 𝒢'
  := sorry

lemma uniqueness_indep_comb' (ρ₁ ρ₂ : @ProbabilityMeasure α (ℰ.1 ⊔ ℱ.1))
  (hρ₁ : indep_comb_measure ℰ ℱ ρ₁) (hρ₂ : indep_comb_measure ℰ ℱ ρ₂) : ρ₁ = ρ₂
  := sorry

end indep_comb

noncomputable instance instPCM {α : Type*} [nonempty : Nonempty α] : PCM (ProbabilitySpace α) where
  binop ℰ ℱ := if h : existence_cond ℰ ℱ
    then Part.some ⟨ℰ.1 ⊔ ℱ.1, Classical.choose h⟩
    else Part.none

-- lemma binop_indep {α : Type*} [nonempty : Nonempty α] (ℰ ℱ : PrSp α) : indep_comb ℰ ℱ (ℰ • ℱ)

lemma inter_diff_space {α : Type*} {m m0 : MeasurableSpace α} {s : Set α} (hm: m ≤ m0) (hs: @MeasurableSet α m s)
  : @MeasurableSet α m0 s := by
    measurability


noncomputable instance instPCM' {α : Type*} [nonempty : Nonempty α] : PCM' (ProbabilitySpace α) where
  one_mul 𝒢 := by

    let one: ProbabilitySpace α := 1 -- can't seem to use dot syntax for 1
    have eq_inf_one: one.1 ⊔ 𝒢.1 = 𝒢.1 := by
      simp only [sup_eq_right]
      exact bot_le
    let ρ := ProbabilitySpace.trim 𝒢.2 (le_of_eq eq_inf_one)
    -- The independent combination exists by case analysis on the σ-algebra of `1`
    have ρ_indep_comb : indep_comb_measure 1 𝒢 ρ := by
      intro e f he hf
      rw [measurableSet_bot_iff] at he
      cases he with
      | inl he_empty => measurability
      | inr he_univ =>
        subst he_univ
        simp_all only [Set.univ_inter, ProbabilityMeasure.coeFn_univ, one_mul,
          ProbabilitySpace.trim_measurableSet_eq, ρ]

    let existence: existence_cond 1 𝒢 := ⟨ρ, ρ_indep_comb⟩

    simp only [PCM.binop, Part.coe_some]
    rw [dite_cond_eq_true (eq_true existence), Part.some_inj]
    let : indep_comb 1 𝒢 𝒢 := sorry
    -- have :

    let that : indep_comb 1 𝒢 (⟨one.1 ⊔ 𝒢.fst, choose existence⟩)
      := by
      rw [indep_comb]
      simp only
      use rfl
      rw [indep_comb_measure]
      intro E F hE hF

      -- rw [trim_measurableSet_eq ]
      have : (ProbabilitySpace.trim (choose existence) (indep_comb._proof_1 1 𝒢 ⟨one.fst ⊔ 𝒢.fst, choose existence⟩
  ((Iff.of_eq (Eq.refl (one.1 ⊔ 𝒢.fst = one.fst ⊔ 𝒢.fst))).mpr rfl))) (E ∩ F) = (choose existence) (E ∩ F) :=
        by
          apply ProbabilitySpace.trim_measurableSet_eq
          refine MeasurableSet.inter ?_ ?_
          · exact inter_diff_space (by exact le_sup_left) hE
          · exact inter_diff_space (by exact le_sup_of_le_right fun s a ↦ a) hF

      rw [this]
      apply choose_spec existence
      · exact hE
      · exact hF

    apply uniqueness_indep_comb 1 𝒢
    · exact that
    · exact this

    -- This is from the design where the uniqueness result works at the granularity of measures.
    -- I think this would remove some bloat from the proof, and I would like to go back to it at
    -- some point

    -- have : ⊥ ⊔ 𝒢.fst = 𝒢.fst := by exact eq_inf_one
    -- rw [this]

    -- have foo (ρ': @ProbabilityMeasure α (one ⊔ 𝒢)) (heq: ρ = ρ'): ⟨one ⊔ 𝒢, ρ'⟩ =  := sorry
    -- let uniqueness := uniqueness_indep_comb 1 𝒢 (instPCM.binop 1 𝒢).volume ρ

    -- The probability measure is precisely that of `P.volume`, because the combination's
    -- σ-algebra is just the same as `P`'s. But in general the probability measure is defined
    -- by the axiom of choice. So the only way is to use 1) the uniqueness of the combination's
    -- measure (via π-λ-theorem), and 2) show that `P`'s measure is a satisfactory instance
  mul_one := sorry
  comm := sorry
  assoc := sorry


-- (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞)
-- instance instPartialOrder {α : Type*} : PartialOrder (ProbabilitySpace α) where

-- instance instKRM {α : Type*} : KRM (ProbabilitySpace α) where
--   ge_mul_mono := sorry

end KRM
