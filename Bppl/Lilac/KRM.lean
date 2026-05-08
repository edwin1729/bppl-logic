/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Mathlib
import Bppl.Lilac.MeasureOnSpace
import Bppl.Lilac.HilbertCube

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

/-
Extract independent product condition from a successful `binop` call.
-/
lemma isIndependentProduct_of_binop_eq_some {p q r : PSpace α}
    (h : @PcmBase.binop _ instPcmBase p q = some r) : r =ᵢ p ⊕ᵢ q := by
  contrapose! h;
  unfold instPcmBase;
  grind +splitImp

/-
Construct a successful `binop` result from an independent product proof.
-/
lemma binop_eq_some_of_isIndependentProduct {p q r : PSpace α}
    (h : r =ᵢ p ⊕ᵢ q) : @PcmBase.binop _ instPcmBase p q = some r := by
  unfold instPcmBase;
  have h_unique : ∃! r, r =ᵢ p ⊕ᵢ q := by
    have := @PSpace.uniqueness α;
    exact ⟨ r, h, fun r' hr' => this _ _ _ _ hr' h ⟩;
  grind

/-
If `p' =ᵢ x' ⊕ᵢ y'`, `x ≤ x'`, `y ≤ y'`, then the trim of `p'` to `x.ms.sum y.ms`
    is an independent product of `x` and `y`.
-/
lemma trim_isIndependentProduct {x x' y y' p' : PSpace α}
    (x_le : x ≤ x') (y_le : y ≤ y') (h_p' : p' =ᵢ x' ⊕ᵢ y')
    (h_ms : x.1.ms.sum y.1.ms ≤ p'.1.ms) :
    (p'.trim h_ms) =ᵢ x ⊕ᵢ y := by
  constructor;
  · rfl;
  · intro E hE F hF;
    convert h_p'.2 E ( x_le.1 _ hE ) F ( y_le.1 _ hF ) using 1;
    · convert MeasureOnSpace.trim_eq h_ms _;
      exact?;
    · rw [ MeasureOnSpace.le_preserves_measure x_le hE, MeasureOnSpace.le_preserves_measure y_le hF ]

def le_mul_mono (x x' y y' p' : PSpace α) (x_le : x ≤ x') (y_le : y ≤ y')
    (ex_ge_mul : x' ⋆ y' = some p') : ∃ p, (x ⋆ y = some p) ∧ p ≤ p' := by
  have h_p' : p' =ᵢ x' ⊕ᵢ y' := isIndependentProduct_of_binop_eq_some ex_ge_mul
  have h_ms : x.1.ms.sum y.1.ms ≤ p'.1.ms := by
    rw [h_p'.1]
    exact MeasurableSpace.sum_mono_both x_le.1 y_le.1
  let p := p'.trim h_ms
  have h_p : p =ᵢ x ⊕ᵢ y := trim_isIndependentProduct x_le y_le h_p' h_ms
  exact ⟨p, binop_eq_some_of_isIndependentProduct h_p, PSpace.trim_le h_ms⟩

noncomputable instance instPcm : Pcm (PSpace α) where
  one_mul := PSpace.one_mul
  comm := PSpace.comm
  assoc := PSpace.assoc

noncomputable instance instKrm : Krm (PSpace α) where
  one_le a := PSpace.le_of_isIndependentProduct_left PSpace.indepenendentProduct_identity
  le_mul_mono := PSpace.le_mul_mono

end PSpace

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

instance : Inhabited HC where
  default := fun _ ↦ 0

open HC

structure PSp extends (PSpace HC) where
  finite_footprint : FiniteFootprint ms

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
  sorry
  -- intro F hF
  -- induction' hF with F hF ih₁ ih₂ ih₃;
  -- · cases' hF with hF hF;
  --   · obtain ⟨ F', hF' ⟩ := ff₁ F hF;
  --     use (fun f => f ∘ Fin.castLE (by
  --     exact le_max_left _ _)) ⁻¹' F'
  --     generalize_proofs at *;
  --     congr! 1;
  --   · obtain ⟨ F', hF' ⟩ := ff₂ F hF;
  --     use (fun x => x ∘ Fin.castLE (by
  --     exact le_max_right _ _)) ⁻¹' F'
  --     generalize_proofs at *;
  --     convert hF' using 1;
  -- · exact ⟨ ∅, by simp +decide ⟩;
  -- · obtain ⟨ F', hF' ⟩ := ih₃; use F'ᶜ; simp +decide [ hF', Set.preimage_compl ] ;
  --   ext; simp [Set.mem_compl_iff, Set.mem_preimage];
  -- · choose! F' hF' using ‹∀ n, ∃ F', _›;
  --   use ⋃ n, F' n; ext; simp +decide [ hF' ] ;

/-
The unit PSpace has finite footprint (trivial σ-algebra depends on 0 coordinates).
-/
lemma ff_unit : FiniteFootprint (PSpace.unit (Ω := HC)).ms := by
  sorry
  -- use 0; simp +decide [ PSpace.unit ] ; (
  -- intro F hF; use if F = Set.univ then Set.univ else ∅; split_ifs <;> simp_all +decide [ Set.ext_iff ] ;
  -- rw [ MeasurableSpace.measurableSet_bot_iff ] at hF ; aesop);

noncomputable instance : One PSp where
  one := ⟨PSpace.unit, ff_unit⟩

/-- If `r =ᵢ p ⊕ᵢ q` and both `p` and `q` have finite footprint, then `r` does too. -/
lemma ff_of_isIndependentProduct {p q r : PSpace HC}
    (h : r =ᵢ p ⊕ᵢ q) (hp : FiniteFootprint p.ms) (hq : FiniteFootprint q.ms) :
    FiniteFootprint r.ms := by
  rw [h.1]
  exact ff_closed_under_sum p.ms q.ms hp hq

noncomputable instance instPcmBase : PcmBase (PSp) where
  binop p q := if h: ∃! r, r =ᵢ p.1 ⊕ᵢ q.1 then
    some ⟨h.choose, ff_of_isIndependentProduct h.choose_spec.1 p.2 q.2⟩
  else none

/-
The original `closed_subtype_Krm` signature requires additional hypotheses
    (injectivity and value-level preservation of binop) to be provable.
    We provide a corrected version with the necessary hypotheses.
-/
def closed_subtype_Krm (α : Type*) [Krm α] (β : Type*) [PcmBase β] (f : β → α)
    (f_inj : Function.Injective f)
    (f_one : f 1 = 1)
    (f_binop : ∀ x y : β, (x ⋆ y).map f = (f x) ⋆ (f y)) : Krm β where
  one_mul a := by
    have h1 : ((1 : β) ⋆ a).map f = some (f a) := by
      rw [f_binop, f_one, Pcm.one_mul]
    cases hab : (1 : β) ⋆ a with
    | none => simp [hab] at h1
    | some b =>
      simp [hab] at h1
      congr; exact f_inj h1
  comm a b := Option.map_injective f_inj (by rw [f_binop, f_binop, Pcm.comm])
  assoc a b c := by
    cases' ‹PcmBase β› with binop;
    cases' ‹Krm α› with binop;
    rename_i h₁ h₂ h₃ h₄;
    have := @binop.assoc;
    convert Option.map_injective f_inj _ using 1;
    convert this ( f a ) ( f b ) ( f c ) using 1;
    · cases h : h₁ a b <;> simp +decide [ ← f_binop, h ];
      rfl;
    · cases h : h₁ b c <;> simp +decide [ ← f_binop, h ];
      simp +decide [ h, Option.map ];
      rfl
  le x y := f x ≤ f y
  le_refl x := le_refl (f x)
  le_trans := fun {_ _ _} h₁ h₂ => @le_trans α _ _ _ _ h₁ h₂
  one_le a := f_one ▸ Krm.one_le (f a)
  le_mul_mono x x' y y' p' hx hy hp := by
    have := ‹Krm α›.le_mul_mono ( f x ) ( f x' ) ( f y ) ( f y' ) ( f p' ) hx hy ( by
      rw [ ← f_binop, hp, Option.map_some ] );
    -- Since $f$ is injective, we can conclude that $x \star y = some p$.
    have h_binop_eq : Option.map f (‹PcmBase β›.binop x y) = some this.choose := by
      exact this.choose_spec.1 ▸ f_binop x y ▸ rfl;
    rw [ Option.map_eq_some_iff ] at h_binop_eq;
    exact ⟨ h_binop_eq.choose, h_binop_eq.choose_spec.1, h_binop_eq.choose_spec.2.symm ▸ this.choose_spec.2 ⟩

/-- The map `PSp → PSpace HC` given by `Subtype.val` preserves the unit. -/
lemma psp_val_one : (1 : PSp).1 = (1 : PSpace HC) := rfl

/-
The map `PSp → PSpace HC` given by `Subtype.val` preserves `binop` values.
-/
lemma psp_val_binop (x y : PSp) : (x ⋆ y).map (·.1) = (x.1 ⋆ y.1) := by
  rw [instPcmBase, PSpace.instPcmBase]
  grind

noncomputable instance : Krm PSp := closed_subtype_Krm (PSpace HC) PSp (·.1)
  (by rintro ⟨a, ha⟩  ⟨b, hb⟩ c; simpa only [mk.injEq])
  rfl
  psp_val_binop

end PSp

namespace Krm_helper
variable {α : Type*} [Krm α]
open PcmBase

@[grind]
lemma exists_right (p q r : α) :
    (binop <$> (binop p q) <*> (some r)).join.isSome → (binop q r).isSome := by
  cases hq : ‹Krm α›.binop q r <;> simp_all +decide;
  have := ‹Krm α›.assoc p q r; aesop;

lemma exists_left (p q r : α) :
    (binop <$> (some p) <*> (binop q r)).join.isSome → (binop p q).isSome := by
  rename_i K;
  have := K.assoc p q r;
  cases h : K.binop p q <;> simp_all +decide;
  exact this.symm

end Krm_helper
