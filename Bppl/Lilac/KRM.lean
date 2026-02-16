
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
class PcmBase (α : Type*) extends One α where
  binop : α → α → Option α -- partial binary operation

notation a:arg " ⋆ " b:arg => PcmBase.binop a b


class Pcm (α : Type*) extends PcmBase α where
  one_mul : ∀ a : α, binop 1 a = a
  mul_one : ∀ a : α, binop a 1 = a
  comm : ∀ a b, binop a b = binop b a
  assoc : ∀ a b c : α,
    binop <$> (binop a b) <*> (some c) = binop <$> (some a) <*> (binop b c)

class Krm (α : Type*) extends Pcm α, Preorder α where
  ge_mul_mono : ∀ x x' y y' p' : α,
    x ≤ x' → y ≤ y' →
    (x' ⋆ y' = some p') → ∃ p, (x ⋆ y = some p) ∧ p ≤ p'

-- Now we want to instantiate this with a probability space
-- We need a type of probability spaces parametrized by given carrier type α

structure PSp (α : Type*) where
  sig : MeasurableSpace α
  vol : Measure α
  is_prob : IsProbabilityMeasure vol

open Classical

-- The relevant lemma for explicitly stating what `⊥` is, is `measurableSet_bot_iff`
noncomputable instance instOne {α : Type*} [nonempty : Nonempty α] : One (PSp α) where
  one := ⟨⊥, @Measure.ofMeasurable α ⊥ (fun s hs ↦ if s = ∅ then 0 else 1) (by simp) sorry,
      -- prove that the measure is a probability measure, μ univ = 1
      ⟨by
        rw [@Measure.ofMeasurable_apply α ⊥]
        · simp
        · exact MeasurableSet.univ
      ⟩
  ⟩

section indep_comb

variable {α : Type*} (ℰ ℱ 𝒢 𝒢': PSp α)

-- why does the R.volume part work? I think the `measure` is a garbage value for sets which
-- are not measurable. But of course this is fine (cause the prop would just be false in
-- garbage value case)
def indep_comb_measure (ρ : @ProbabilityMeasure α (ℰ.1 ⊔ ℱ.1)) :=
    ∀ E F : Set α, MeasurableSet[ℰ.1] E → MeasurableSet[ℱ.1] F →
      ρ (E ∩ F) = ℰ.2 E * ℱ.2 F

-- The problem with the above is that it forces the measurablespace to be `ℰ.1 ⊔ ℱ.1`
-- We don't want that.
def indep_comb_measure' (𝒢 : PSp α) (ρ : @ProbabilityMeasure α (ℰ.1 ⊔ ℱ.1)) :=
    𝒢.1 = (ℰ.1 ⊔ ℱ.1) ∧
    ∀ E F : Set α, MeasurableSet[ℰ.1] E → MeasurableSet[ℱ.1] F →
      ρ (E ∩ F) = ℰ.2 E * ℱ.2 F

def existence_cond : Prop := ∃ ρ, indep_comb_measure ℰ ℱ ρ

end indep_comb

noncomputable instance instPcmBase {α : Type*} [nonempty : Nonempty α] : PcmBase (PSp α) where
  binop ℰ ℱ := if h : existence_cond ℰ ℱ
    then some ⟨ℰ.1 ⊔ ℱ.1, (Classical.choose h).1, (Classical.choose h).2 ⟩
    else none

-- lemma binop_indep {α : Type*} [nonempty : Nonempty α] (ℰ ℱ : PrSp α) : indep_comb ℰ ℱ (ℰ ⋆ ℱ)

lemma inter_diff_space {α : Type*} {m m0 : MeasurableSpace α} {s : Set α} (hm: m ≤ m0) (hs: @MeasurableSet α m s)
  : @MeasurableSet α m0 s := by
    measurability

noncomputable instance instPcm {α : Type*} [nonempty : Nonempty α] : Pcm (PSp α) where
  one_mul 𝒢 := sorry
  mul_one := sorry
  comm := sorry
  assoc := sorry

noncomputable instance instPartialOrder {α : Type*} : PartialOrder (PSp α) where
  le ℰ ℱ := ∀ h : ℰ.sig ≤ ℱ.sig, ℰ.vol = ℱ.vol.trim h
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

noncomputable instance instKrm {α : Type*} [nonempty : Nonempty α] : Krm (PSp α) where
  ge_mul_mono := sorry

end KRM
