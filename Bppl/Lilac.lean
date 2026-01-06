import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

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
  binop : α → α → Option α -- partial binary operation

notation a:arg " • " b:arg => PCM.binop a b

class PCM' (α : Type*) extends PCM α where
  one_mul : ∀ a : α, binop 1 a = a
  mul_one : ∀ a : α, binop a 1 = a
  comm : ∀ a b, binop a b = binop b a
  assoc : ∀ a b c : α,
    (binop a b) >>= (fun ab => (binop ab c)) =
    (binop b c) >>= (fun bc => (binop a bc))

class KRM (α : Type*) extends PCM' α, PartialOrder α where
  ge_mul_mono : ∀ x x' y y' p' : α,
    x ≤ x' → y ≤ y' →
    (x' • y' = some p') → ∃ p, (x • y = some p) ∧  p ≤ p'

-- Now we want to instantiate this with a probability space
-- We need a type of probability spaces parametrized by given carrier type α

def ProbabilitySpace (α : Type*) := Σ (m: MeasurableSpace α), @ProbabilityMeasure α m

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

end indep_comb

noncomputable instance instPCM {α : Type*} [nonempty : Nonempty α] : PCM (ProbabilitySpace α) where
  binop ℰ ℱ := if h : existence_cond ℰ ℱ
    then some ⟨ℰ.1 ⊔ ℱ.1, Classical.choose h⟩
    else none

-- lemma binop_indep {α : Type*} [nonempty : Nonempty α] (ℰ ℱ : PrSp α) : indep_comb ℰ ℱ (ℰ • ℱ)

lemma inter_diff_space {α : Type*} {m m0 : MeasurableSpace α} {s : Set α} (hm: m ≤ m0) (hs: @MeasurableSet α m s)
  : @MeasurableSet α m0 s := by
    measurability

noncomputable instance instPCM' {α : Type*} [nonempty : Nonempty α] : PCM' (ProbabilitySpace α) where
  one_mul 𝒢 := sorry
  mul_one := sorry
  comm := sorry
  assoc := sorry

noncomputable instance instPartialOrder {α : Type*} : PartialOrder (ProbabilitySpace α) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

noncomputable instance instKRM {α : Type*} [nonempty : Nonempty α] : KRM (ProbabilitySpace α) where
  ge_mul_mono := sorry

end KRM

open Iris.BI Iris

abbrev PROP (α : Type*) [nonempty : Nonempty α] := ProbabilitySpace α → Prop

instance instBIBase {α : Type*} [nonempty : Nonempty α]: BIBase (PROP α ) where
  Entails P Q      := ∀ σ, P σ → Q σ
  emp            σ := σ = 1
  pure φ         _ := φ
  and P Q        σ := P σ ∧ Q σ
  or P Q         σ := P σ ∨ Q σ
  imp P Q        σ := P σ → Q σ
  sForall Ψ      σ := ∀ p, Ψ p → p σ
  sExists Ψ      σ := ∃ p, Ψ p ∧ p σ
  sep P Q        σ := ∃ σ1 σ2 : ProbabilitySpace α, σ1 • σ2 = some σ ∧ P σ1 ∧ Q σ2
  wand P Q       σ := ∀ σ' : ProbabilitySpace α, (h : (σ • σ').isSome) → P σ' → Q ((σ • σ').get h)
  -- could we do better than this? Identify what more is persistent/affine
  -- wasn't BaSL partially affine? What does that mean?
  persistently P _ := P 1
  later P        σ := P σ -- there is no step indexing

instance {α : Type*} [nonempty : Nonempty α] : COFE (PROP α) := COFE.ofDiscrete Eq equivalence_eq

instance instBI {α : Type*} [nonempty : Nonempty α] : BI (PROP α) where
  equiv_iff := sorry
  entails_preorder := sorry
  and_ne := sorry
  or_ne := sorry
  imp_ne := sorry
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := sorry
  wand_ne := sorry
  persistently_ne := sorry
  later_ne := sorry
  pure_intro := sorry
  pure_elim' := sorry
  and_elim_l := sorry
  and_elim_r := sorry
  and_intro := sorry
  or_intro_l := sorry
  or_intro_r := sorry
  or_elim := sorry
  imp_intro := sorry
  imp_elim := sorry
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := sorry
  emp_sep := sorry
  sep_symm := sorry
  sep_assoc_l := sorry
  wand_intro := sorry
  wand_elim := sorry
  persistently_mono := sorry
  persistently_idem_2 := sorry
  persistently_emp_2 := sorry
  persistently_and_2 := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l := sorry
  persistently_and_l := sorry
  later_mono := sorry
  later_intro := sorry
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := sorry
  later_persistently := sorry
  later_false_em := sorry
