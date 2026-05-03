/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Mathlib.Data.PFun
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Bppl.Lilac.MeasureOnSpace

/- Instantiating the Kripke Resource Monoid according to  Lilac -/

open MeasureTheory MeasurableSpace
-- set_option quotPrecheck false
/-- Partial Commutative Monoid -/
class PcmBase (α : Type*) extends One α where
  binop : α → α → Option α -- partial binary operation

notation a:arg " ⋆ " b:arg => PcmBase.binop a b

class Pcm (α : Type*) extends PcmBase α where
  one_mul : ∀ a : α, binop 1 a = a
  comm : ∀ a b, binop a b = binop b a
  assoc : ∀ a b c : α,
    (binop <$> (binop a b) <*> (some c)).join = (binop <$> (some a) <*> (binop b c)).join

class Krm (α : Type*) extends Pcm α, Preorder α where
  one_le : ∀ (a : α), 1 ≤ a
  le_mul_mono : ∀ x x' y y' p' : α,
    x ≤ x' → y ≤ y' →
    (x' ⋆ y' = some p') → ∃ p, (x ⋆ y = some p) ∧ p ≤ p'

namespace PSpace
open Classical PcmBase PSpace
variable {α : Type*} [Inhabited α]
noncomputable instance instPcmBase : PcmBase (PSpace α) where
  binop p q := if h: ∃! r, r =ᵢ p ⊕ᵢ q then some h.choose else none

@[grind =]
lemma one_mul (p : PSpace α) : binop 1 p = p := by
  change (if h: ∃! r, r =ᵢ unit ⊕ᵢ p then some h.choose else none) = some p
  have comb : ∃! r, r =ᵢ unit ⊕ᵢ p := existsUnique_of_exists_of_unique
      ⟨p, indepenendentProduct_identity⟩ (uniqueness unit p)
  rw [dif_pos comb]
  simp only [Option.some.injEq]
  rw [ExistsUnique.choose_eq_iff comb]
  exact indepenendentProduct_identity

@[grind =]
lemma comm (p q : PSpace α) : binop p q = binop q p := by
  by_cases h₁: ∃ r, r =ᵢ p ⊕ᵢ q
  · by_cases h₂: ∃ r, r =ᵢ q ⊕ᵢ p
    · -- The nontrivial case where both the independent product exists
      have h₁' : ∃! r, r =ᵢ p ⊕ᵢ q := existsUnique_of_exists_of_unique h₁ (uniqueness p q)
      have h₂' : ∃! r, r =ᵢ q ⊕ᵢ p := existsUnique_of_exists_of_unique h₂ (uniqueness q p)
      dsimp [PcmBase.binop]
      rw [dif_pos h₁', dif_pos h₂',
        Option.some.injEq, ExistsUnique.choose_eq_iff h₁']
      apply independentProduct_comm
      rw [← ExistsUnique.choose_eq_iff h₂']
    · -- The product can't exist one way but not the other
      have : ∃ r, r =ᵢ q ⊕ᵢ p := by
        obtain ⟨r, hr⟩ := h₁
        exact ⟨r, independentProduct_comm hr⟩
      contradiction
  · by_cases h₂: ∃ r, r =ᵢ q ⊕ᵢ p
    · -- The product can't exist one way but not the other
      have : ∃ r, r =ᵢ p ⊕ᵢ q := by
        obtain ⟨r, hr⟩ := h₂
        exact ⟨r, independentProduct_comm hr⟩
      contradiction
    · -- The product doesn't exist
      have h_none₁ : q ⋆ p = none := by
        apply dite_cond_eq_false
        simp_all only [not_exists, existsUnique_false]
      have h_none₂ : p ⋆ q = none := by
        apply dite_cond_eq_false
        simp_all only [not_exists, existsUnique_false]
      rw [h_none₁, h_none₂]

lemma assoc (p q r : PSpace α) :
    (binop <$> (binop p q) <*> (some r)).join = (binop <$> (some p) <*> (binop q r)).join := by
  by_cases h_pq: ∃ pq, pq =ᵢ p ⊕ᵢ q
  · by_cases h_qr: ∃ qr, qr =ᵢ q ⊕ᵢ r
    · have h_pq' : ∃! pq, pq =ᵢ p ⊕ᵢ q := existsUnique_of_exists_of_unique h_pq (uniqueness p q)
      obtain ⟨pq, h_pq⟩ := h_pq'
      by_cases h_pq_r: ∃ s, s =ᵢ pq ⊕ᵢ r
      · have h_qr' : ∃! qr, qr =ᵢ q ⊕ᵢ r := existsUnique_of_exists_of_unique h_qr (uniqueness q r)
        obtain ⟨qr, h_qr⟩ := h_qr'
        by_cases h_p_qr: ∃ s, s =ᵢ p ⊕ᵢ qr
        · -- (1) The "interesting" case where all independent products exist
          have h_pq_r' : ∃! s, s =ᵢ pq ⊕ᵢ r
            := existsUnique_of_exists_of_unique h_pq_r (uniqueness pq r)
          have h_p_qr' : ∃! s, s =ᵢ p ⊕ᵢ qr
            := existsUnique_of_exists_of_unique h_p_qr (uniqueness p qr)
          dsimp [PcmBase.binop]
          rw [dif_pos ⟨pq, h_pq⟩, dif_pos ⟨qr, h_qr⟩]
          dsimp only [Option.map_some, Option.seq_some, Option.join_some]
          have h_pq' : ∃! pq, pq =ᵢ p ⊕ᵢ q := ⟨pq, h_pq⟩
          have h_qr' : ∃! qr, qr =ᵢ q ⊕ᵢ r := ⟨qr, h_qr⟩
          have heq₁ : h_pq'.choose = pq := (ExistsUnique.choose_eq_iff h_pq').2 h_pq.1
          have heq₂ : h_qr'.choose = qr := (ExistsUnique.choose_eq_iff h_qr').2 h_qr.1
          rw [heq₁, heq₂]
          rw [dif_pos h_pq_r', dif_pos h_p_qr', Option.some.injEq]
          rw [ExistsUnique.choose_eq_iff h_pq_r']
          suffices ∃ pq, pq =ᵢ p ⊕ᵢ q ∧ h_p_qr'.choose =ᵢ pq ⊕ᵢ r by
            obtain ⟨pq', h_pq'⟩ := this
            have eq : pq' = pq := uniqueness p q pq' pq h_pq'.1 h_pq.1
            exact eq ▸ h_pq'.2
          apply independentProduct_assoc_right h_qr.1
          exact (Exists.choose_spec h_p_qr').1
        · -- (2) lhs = some rhs = none
          obtain ⟨s, h_s⟩ := h_pq_r
          have : ∃ s, s =ᵢ p ⊕ᵢ qr := by
            obtain ⟨qr', h_qr'⟩ := independentProduct_assoc h_pq.1 h_s
            have eq : qr' = qr := uniqueness q r qr' qr h_qr'.1 h_qr.1
            exact ⟨s, eq ▸ h_qr'.2⟩
          contradiction
      · have h_qr' : ∃! qr, qr =ᵢ q ⊕ᵢ r := existsUnique_of_exists_of_unique h_qr (uniqueness q r)
        obtain ⟨qr, h_qr⟩ := h_qr'
        by_cases h_p_qr : ∃ s, s =ᵢ p ⊕ᵢ qr
        · -- (3) lhs = none rhs = some. dual to (2)
          obtain ⟨s, h_s⟩ := h_p_qr
          have : ∃ s, s =ᵢ pq ⊕ᵢ r := by
            obtain ⟨pq', h_pq'⟩ := independentProduct_assoc_right h_qr.1 h_s
            have eq : pq' = pq := uniqueness p q pq' pq h_pq'.1 h_pq.1
            exact ⟨s, eq ▸ h_pq'.2⟩
          contradiction
        · -- (4) none_left copied from (6) none_right from (8)
          have none_left : (binop <$> p ⋆ q <*> some r).join = none := by
            have some_pq : p ⋆ q = some pq := by
              dsimp [binop]
              rw [dif_pos ⟨pq, h_pq⟩, Option.some.injEq,
                ExistsUnique.choose_eq_iff ⟨pq, h_pq⟩]
              exact h_pq.1
            rw [some_pq]
            dsimp only [Option.map_eq_map, Option.map_some, Option.seq_some, Option.join_some]
            apply dite_cond_eq_false
            simp_all only [not_exists, existsUnique_false]
          have none_right : (binop <$> some p <*> q ⋆ r).join = none := by
            have some_qr : q ⋆ r = some qr := by
              dsimp [binop]
              rw [dif_pos ⟨qr, h_qr⟩, Option.some.injEq,
                ExistsUnique.choose_eq_iff ⟨qr, h_qr⟩]
              exact h_qr.1
            rw [some_qr]
            dsimp only [Option.map_eq_map, Option.map_some, Option.seq_some, Option.join_some]
            apply dite_cond_eq_false
            simp_all only [not_exists, existsUnique_false]
          rw [none_left, none_right]
    · -- rhs = none
      have h_pq' : ∃! pq, pq =ᵢ p ⊕ᵢ q := existsUnique_of_exists_of_unique h_pq (uniqueness p q)
      obtain ⟨pq, h_pq⟩ := h_pq'
      by_cases h_pq_r: ∃ s, s =ᵢ pq ⊕ᵢ r
      · -- (5) lhs = some _    so contradiction
        obtain ⟨s, h_s⟩ := h_pq_r
        have : ∃ qr, qr =ᵢ q ⊕ᵢ r := by
          obtain ⟨qr, h_qr, _⟩  := independentProduct_assoc h_pq.1 h_s
          exact ⟨qr, h_qr⟩
        contradiction
      · -- (6) lhs = none
        have none_left : (binop <$> p ⋆ q <*> some r).join = none := by
          have some_pq : p ⋆ q = some pq := by
            dsimp [binop]
            rw [dif_pos ⟨pq, h_pq⟩, Option.some.injEq,
              ExistsUnique.choose_eq_iff ⟨pq, h_pq⟩]
            exact h_pq.1
          rw [some_pq]
          dsimp only [Option.map_eq_map, Option.map_some, Option.seq_some, Option.join_some]
          apply dite_cond_eq_false
          simp_all only [not_exists, existsUnique_false]
        have none_right : (binop <$> some p <*> q ⋆ r).join = none := by
          have none_qr : q ⋆ r = none := by
            apply dite_cond_eq_false
            simp_all only [not_exists, existsUnique_false]
          rw [none_qr]
          rfl
        rw [none_left, none_right]
  · -- lhs = none
    by_cases h_qr: ∃ qr, qr =ᵢ q ⊕ᵢ r
    · have h_qr' : ∃! qr, qr =ᵢ q ⊕ᵢ r := existsUnique_of_exists_of_unique h_qr (uniqueness q r)
      obtain ⟨qr, h_qr⟩ := h_qr'
      by_cases h_p_qr: ∃ s, s =ᵢ p ⊕ᵢ qr
      · -- (7) rhs = some _     so contradiction
        obtain ⟨s, h_s⟩ := h_p_qr
        have : ∃ pq, pq =ᵢ p ⊕ᵢ q := by
          obtain ⟨pq, h_pq, _⟩  := independentProduct_assoc_right h_qr.1 h_s
          exact ⟨pq, h_pq⟩
        contradiction
      · -- (8) rhs = none
        have none_left : (binop <$> p ⋆ q <*> some r).join = none := by
          have none_pq : p ⋆ q = none := by
            apply dite_cond_eq_false
            simp_all only [not_exists, existsUnique_false]
          rw [none_pq]
          rfl
        have none_right : (binop <$> some p <*> q ⋆ r).join = none := by
          have some_qr : q ⋆ r = some qr := by
            dsimp [binop]
            rw [dif_pos ⟨qr, h_qr⟩, Option.some.injEq,
              ExistsUnique.choose_eq_iff ⟨qr, h_qr⟩]
            exact h_qr.1
          rw [some_qr]
          dsimp only [Option.map_eq_map, Option.map_some, Option.seq_some, Option.join_some]
          apply dite_cond_eq_false
          simp_all only [not_exists, existsUnique_false]
        rw [none_left, none_right]
    · -- (9) rhs = none     copied verbatim none_left from (8) and none_right (6)
      have none_left : (binop <$> p ⋆ q <*> some r).join = none := by
        have none_pq : p ⋆ q = none := by
          apply dite_cond_eq_false
          simp_all only [not_exists, existsUnique_false]
        rw [none_pq]
        rfl
      have none_right : (binop <$> some p <*> q ⋆ r).join = none := by
        have none_qr : q ⋆ r = none := by
          apply dite_cond_eq_false
          simp_all only [not_exists, existsUnique_false]
        rw [none_qr]
        rfl
      rw [none_left, none_right]


def le_mul_mono (x x' y y' p' : PSpace α) (x_le : x ≤ x') (y_le : y ≤ y')
    (ex_ge_mul : x' ⋆ y' = some p') : ∃ p, (x ⋆ y = some p) ∧ p ≤ p' := by
  sorry

noncomputable instance instPcm : Pcm (PSpace α) where
  one_mul := PSpace.one_mul
  comm := PSpace.comm
  assoc := PSpace.assoc

noncomputable instance instKrm : Krm (PSpace α) where
  one_le := sorry
  le_mul_mono := PSpace.le_mul_mono

end PSpace

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

instance : Inhabited HC where
  default := fun _ ↦ 0

abbrev borel_ms_HC : MeasurableSpace HC := MeasurableSpace.pi

/-- Splitting at first n coordinates of `HC` (Hilbert Cube) is isomorphic to `HC`. -/
noncomputable def HC.splitMeasEquiv (n : ℕ) :
    HC ≃ᵐ (Fin n → Set.Icc (0:ℝ) 1) × HC :=
  (MeasurableEquiv.piCongrLeft (fun _ => Set.Icc (0:ℝ) 1) (finSumNatEquiv n)).symm |>.trans
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => Set.Icc (0:ℝ) 1))

/-- The σ-algebra is only "interesting" in the first `n` coordinates for some finite `n`.
In the rest of the coordinates, its the `univ` set. -/
def FiniteFootprint (ms : MeasurableSpace HC) : Prop :=
  ∃ n : ℕ, ∀ F : Set HC, MeasurableSet[ms] F →
    ∃ F' : Set (Fin n → Set.Icc (0:ℝ) 1),
      F = HC.splitMeasEquiv n ⁻¹' (F' ×ˢ (@Set.univ HC))

-- structure PSp extends (PSpace HC) where
--   finite_footprint : FiniteFootprint ms

abbrev PSp := {p : PSpace HC // FiniteFootprint p.ms}

namespace PSp
open Classical

prefix:max "✓'" => Option.isSome

abbrev coerceOption {α : Type*} {x : Option α} (h : x.isSome) := x.get h

prefix:max "↓" => coerceOption

lemma ff_closed_under_sum (ms₁ ms₂ : MeasurableSpace HC) (hms₁ : FiniteFootprint ms₁)
    (hms₂ : FiniteFootprint ms₂) : FiniteFootprint (ms₁.sum ms₂) := by
  obtain ⟨n₁, ff₁⟩ := hms₁
  obtain ⟨n₂, ff₂⟩ := hms₂
  use max n₁ n₂
  intro F hF
  sorry

noncomputable instance : One PSp where
  one := ⟨PSpace.unit, sorry⟩

noncomputable instance instPcmBase : PcmBase (PSp) where
  binop p q := if h: ∃! r, r =ᵢ p.1 ⊕ᵢ q.1 then some ⟨h.choose, sorry⟩ else none

def closed_subtype_Krm (α : Type*) [Krm α] (β : Type*) [PcmBase β] (f : β → α)
    (one : f 1 = 1) (indep_prod : ∀ x y : β, ✓'(x ⋆ y) ↔ ✓'((f x) ⋆ (f y))) : Krm β := sorry

-- def closed_subtype_Krm (α : Type*) [Krm α] (P : α → Prop) [PcmBase {α // P α}]
--     (closed : ∀ x y : {α // P α}, ✓'(x ⋆ y) ↔ ✓'(x.1 ⋆ y.1)) : Krm {α // P α} := sorry

noncomputable instance : Krm PSp := closed_subtype_Krm (PSpace HC) PSp (·.1) sorry sorry

end PSp

namespace Krm_helper
variable {α : Type*} [Krm α]
open PcmBase
@[grind]
lemma exists_right (p q r : α) :
    (binop <$> (binop p q) <*> (some r)).join.isSome → (binop q r).isSome := by
  sorry

lemma exists_left (p q r : α) :
    (binop <$> (some p) <*> (binop q r)).join.isSome → (binop p q).isSome := by
  sorry

end Krm_helper
