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

    -- Measure.ofMeasurable (fun s hs ↦
    --     let foo: s = ∅ ∨ s = Set.univ := by grind [MeasurableSpace.generateFrom]
    --     1
    --  )

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

  -- My glorious non-circular definitionh
  -- ∀ e f₁ f₂ : Set α, MeasurableSet e → MeasurableSet f₁ → MeasurableSet f₂ →
  --   E.volume (e ∩ f₁) / E.volume (e ∩ f₂) = F.volume f₁ / F.volume f₂

lemma indep_existence {α : Type*}
  (P : ProbabilitySpace α) (Q : ProbabilitySpace α) (hPQ : existence_cond P Q) :
  ∃ R : ProbabilitySpace α, indep_combination_pred P Q R :=
  -- use dynkin's pi lambda theorem. Nope that's completely wrong
  sorry

-- def indep_combination {α : Type*}
--   (P : ProbabilitySpace α) (Q : ProbabilitySpace α) :
--   ProbabilitySpace α :=
--   if h : ∃ R : ProbabilitySpace α, indep_combination_pred P Q R then
--     Classical.choose h
--   else
--     foo α

abbrev existence_cond {α : Type*} (E : ProbabilitySpace α) (F : ProbabilitySpace α) :=
  ∃ ρ : @Measure α (E.toMeasurableSpace ⊓ F.toMeasurableSpace),
    ∀ e f : Set α, MeasurableSet[E] e → MeasurableSet[F] f → ρ (e ∩ f) = E.volume e * F.volume f

open Classical
instance instPCM {α : Type*} [nonempty : Nonempty α] : PCM (ProbabilitySpace α) where
  binop E F := if h : ∃ ρ : @Measure α (E.toMeasurableSpace ⊓ F.toMeasurableSpace),
    ∀ e f : Set α, MeasurableSet[E] e → MeasurableSet[F] f → ρ (e ∩ f) = E.volume e * F.volume f then
      let foo := Classical.choose h
      Part.some {
        toMeasurableSpace := E.toMeasurableSpace ⊓ F.toMeasurableSpace
        volume := foo
        is_prob := ⟨by simp⟩
      }
    else Part.none
  one_mul := sorry
  mul_one := sorry
  comm := sorry
  assoc := sorry

-- instance instPartialOrder {α : Type*} : PartialOrder (ProbabilitySpace α) where

-- instance instKRM {α : Type*} : KRM (ProbabilitySpace α) where
--   ge_mul_mono := sorry


-- def foo (α : Type*) : ProbabilitySpace α := {
--   MeasurableSet' := fun s => s = ∅ ∨ s = Set.univ,
--   measurableSet_empty := Or.inl rfl,
--   measurableSet_compl := by simp,
--   measurableSet_iUnion := by
--     intros f hf
--     by_cases h : ∃ i, f i = Set.univ
--     · right
--       obtain ⟨i, h⟩ := h
--       have ge : f i ⊆ ⋃ i, f i := Set.subset_iUnion f i
--       simp_all only [Set.univ_subset_iff]
--     · left
--       rw [Set.iUnion_eq_empty]
--       intro i
--       rw [not_exists] at h
--       simp_all only [or_false],
--   volume := Measure.dirac ∅,
-- }

-- def foo' (α : Type*) : ProbabilityMeasure α

-- instance (α : Type) : One (ProbabilitySpace α) where
--   one := foo α

-- define a predicate.
-- define an existence condition


end KRM
