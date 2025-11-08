import Iris.BI.BIBase
import Mathlib.Data.PFun
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory
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

noncomputable instance instOne {α : Type*} [nonempty : Nonempty α] : One (ProbabilitySpace α) where
  one := {
    toMeasurableSpace := ⊥
    -- below magic provided by @p127 discord, Aaron Liu
    volume := ⟨@OuterMeasure.toMeasure α ⊥ (OuterMeasure.dirac (Classical.choice nonempty)) bot_le,
      ⟨by simp⟩⟩
  }

instance {α : Type*} : Coe (ProbabilitySpace α) (MeasurableSpace α) where
  coe P := P.toMeasurableSpace

-- TODO fix the need to do `toMeasurableSpace`. It's annoying
-- notation "∀ " s:arg " ∈ᵐ " P:arg ", " body:arg => ∀ s, MeasurableSet[P] s → body
-- on that topic, maybe I should use a strucutre and just use a pair
-- ⟨Measurable Space α, Measure α⟩, which is the more standard way in mathlib

-- why does the R.volume part work? I think the `measure` is a garbage value for sets which
-- are not measurable. But of course this is fine (cause the prop would just be false in
-- garbage value case)
def indep_combination_pred {α : Type*}
  (P : ProbabilitySpace α) (Q : ProbabilitySpace α) (R : ProbabilitySpace α) : Prop :=
  P.toMeasurableSpace ⊓ Q.toMeasurableSpace = R.toMeasurableSpace ∧
  ∀ p q : Set α, MeasurableSet[P] p → MeasurableSet[Q] q →
    P.volume p * Q.volume q = R.volume (p ∩ q)

abbrev existence_cond {α : Type*} (E : ProbabilitySpace α) (F : ProbabilitySpace α) :=
  ∃ ρ : @ProbabilityMeasure α (E.toMeasurableSpace ⊓ F.toMeasurableSpace),
    ∀ e f : Set α, MeasurableSet[E] e → MeasurableSet[F] f → ρ (e ∩ f) = E.volume e * F.volume f

open Classical
instance instPCM {α : Type*} [nonempty : Nonempty α] : PCM (ProbabilitySpace α) where
  binop E F := if h : existence_cond E F
    then Part.some {
        toMeasurableSpace := E.toMeasurableSpace ⊓ F.toMeasurableSpace
        volume := Classical.choose h
      }
    else Part.none
  one_mul := sorry
  mul_one := sorry
  comm := sorry
  assoc := sorry

-- instance instPartialOrder {α : Type*} : PartialOrder (ProbabilitySpace α) where

-- instance instKRM {α : Type*} : KRM (ProbabilitySpace α) where
--   ge_mul_mono := sorry

end KRM
