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
  one_mul : ∀ a : α, binop 1 a = a
  mul_one : ∀ a : α, binop a 1 = a
  comm : ∀ a b, binop a b = binop b a
  assoc : ∀ a b c : α,
    (binop a b) >>= (fun ab => (binop ab c)) =
    (binop b c) >>= (fun bc => (binop a bc))

notation a:arg " • " b:arg => PCM.binop a b

class KRM (α : Type*) extends PCM α, PartialOrder α where
  ge_mul_mono : ∀ x x' y y' p' : α,
    x ≤ x' → y ≤ y' →
    (x' • y' = some p') → ∃ p, (x • y = some p) ∧  p ≤ p'

-- Now we want to instantiate this with a probability space
-- We need a type of probability spaces parametrized by given carrier type α

class ProbabilitySpace (α : Type*) extends MeasurableSpace α where
  volume : ProbabilityMeasure α

namespace ProbabilitySpace

variable {α : Type*} {m m0 : MeasurableSpace α}

instance : Coe (ProbabilitySpace α) (MeasurableSpace α) where
  coe P := P.toMeasurableSpace

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
  one := {
    toMeasurableSpace := ⊥
    volume := ⟨@Measure.ofMeasurable α ⊥ (fun s hs ↦ if s = ∅ then 0 else 1) (by simp) sorry,
      -- prove that the measure is a probability measure, μ univ = 1
      ⟨by
        rw [@Measure.ofMeasurable_apply α ⊥]
        · simp
        · exact MeasurableSet.univ
      ⟩⟩
  }

section indep_comb

variable {α : Type*} (ℰ : ProbabilitySpace α) (ℱ : ProbabilitySpace α)

-- At the moment I talk explicitly about properties of combinations of measures
-- (uniqueness/existence). These are trivial for spaces. However it may be cleaner later on
-- to talk of the space as a whole instead

-- TODO fix the need to do `toMeasurableSpace`. It's annoying
-- notation "∀ " s:arg " ∈ᵐ " P:arg ", " body:arg => ∀ s, MeasurableSet[P] s → body
-- on that topic, maybe I should use a strucutre and just use a pair
-- ⟨Measurable Space α, Measure α⟩, which is the more standard way in mathlib

-- why does the R.volume part work? I think the `measure` is a garbage value for sets which
-- are not measurable. But of course this is fine (cause the prop would just be false in
-- garbage value case)
def indep_comb_measure (ρ : @ProbabilityMeasure α (ℰ ⊔ ℱ)) :=
    ∀ E F : Set α, MeasurableSet[ℰ] E → MeasurableSet[ℱ] F →
      ρ (E ∩ F) = ℰ.volume E * ℱ.volume F

def existence_cond : Prop := ∃ ρ, indep_comb_measure ℰ ℱ ρ

-- use the π-λ-theorem here
def uniqueness_indep_comb (ρ₁ ρ₂ : @ProbabilityMeasure α (ℰ ⊔ ℱ))
  (hρ₁ : indep_comb_measure ℰ ℱ ρ₁) (hρ₂ : indep_comb_measure ℰ ℱ ρ₂) := ρ₁ = ρ₂

end indep_comb

noncomputable instance instPCM {α : Type*} [nonempty : Nonempty α] : PCM (ProbabilitySpace α) where
  binop E F := if h : existence_cond E F
    then Part.some {
        toMeasurableSpace := E.toMeasurableSpace ⊔ F.toMeasurableSpace
        -- It looks uniqueness need not be proven? What does uniqueness afford us?
        volume := Classical.choose h
      }
    else Part.none
  one_mul P := by
    let one: ProbabilitySpace α := 1 -- can't seem to use dot syntax for 1
    -- The indepdenent combination exists by case analysis on the σ-algebra of `1`
    have existence: existence_cond 1 P := by
      have eq_inf_one: one.toMeasurableSpace ⊔ P.toMeasurableSpace = P.toMeasurableSpace := by
        simp only [sup_eq_right]
        exact bot_le
      use ProbabilitySpace.trim P.volume (le_of_eq eq_inf_one)
      intro e f he hf
      rw [measurableSet_bot_iff] at he

      cases he with
      | inl he_empty => measurability
      | inr he_univ =>
        subst he_univ
        simp_all only [Set.univ_inter, ProbabilityMeasure.coeFn_univ, one_mul,
          ProbabilitySpace.trim_measurableSet_eq]

    rw [dite_cond_eq_true (eq_true existence)]
    simp only [Part.coe_some, Part.some_inj]

    -- The probability measure is precisely that of `P.volume`, because the combination's
    -- σ-algebra is just the same as `P`'s. But in general the probability measure is defined
    -- by the axiom of choice. So the only way is to use 1) the uniqueness of the combination's
    -- measure (via π-λ-theorem), and 2) show that `P`'s measure is a satisfactory instance
    sorry
  mul_one := sorry
  comm := sorry
  assoc := sorry


-- (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞)
-- instance instPartialOrder {α : Type*} : PartialOrder (ProbabilitySpace α) where

-- instance instKRM {α : Type*} : KRM (ProbabilitySpace α) where
--   ge_mul_mono := sorry

end KRM
