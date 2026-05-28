/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.MeasureOnSpace
import Bppl.Lilac.Std

/-! # KRMs on Probability Spaces and Probability Spaces with Finite Footprint

Here we define a Kripke Resource Monoid (KRM), instantiate it to with probability spaces and
instantiate it again with the subspaces of probability spaces with finite footprint.

In this file the decision to use a KRM as is, without further building an Ordered Unital Resource
Algebra. The latter introduces some more structure to the latter to avoid working with `Option`
types. In restrospect after witnessing the messiness of the `Option` type, perhaps the project
should be refactored to using Order Unital Resource Algebras afterall.

## Main Definitions
- `Krm`: Extends `Pcm` (Partial Commutative Monoid) with a `Preorder` and imposes some additional
laws. Note that we add the law `one_le` which is an optional law which turns the `Krm` into a
generator of only Affine separatin logics.
- `PSpace.Krm.instKrm`: `PSpace` (Probability Spaces) form a `Krm`
- `PSp`: A subtype of `PSpace` which additionally enforces `FiniteFootprint` on its
`MeasurableSpace`
- `PSp.instKrm`: Using `closed_subtype_Krm` to show that `PSp` is also a `Krm`

## Main Statements
- `closed_subtype_Krm`: If in a subspace of an existing `Krm`, the binary operation is closed, then
the subspace is a `Krm`

The namespace `Krm` at the end of the file provides various helpers to form an API of
lemmas derived from the Krm laws.
-/

open MeasureTheory MeasurableSpace
-- set_option quotPrecheck false
/-- Partial Commutative Monoid -/
class PcmBase (α : Type*) extends One α where
  binop : α → α → Option α -- partial binary operation

notation a:arg " ⋆ " b:arg => PcmBase.binop a b

class Pcm (α : Type*) extends PcmBase α where
  one_mul (a : α) : 1 ⋆ a = a
  comm (a b : α) : a ⋆ b = b ⋆ a
  assoc (a b c : α) :
    (binop <$> (a ⋆ b) <*> (some c)).join = (binop <$> (some a) <*> (b ⋆ c)).join

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

namespace Pcm

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
          obtain ⟨qr, h_qr, _⟩ := independentProduct_assoc h_pq.1 h_s
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
          obtain ⟨pq, h_pq, _⟩ := independentProduct_assoc_right h_qr.1 h_s
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

noncomputable instance instPcm : Pcm (PSpace α) where
  one_mul := one_mul
  comm := comm
  assoc := assoc

end Pcm

namespace Krm

/- Extract independent product condition from a successful `binop` call.  -/
lemma isIndependentProduct_of_binop_eq_some {p q r : PSpace α}
    (h : p ⋆ q = some r) : r =ᵢ p ⊕ᵢ q := by
  contrapose! h;
  unfold instPcmBase;
  grind +splitImp

/- Construct a successful `binop` result from an independent product proof.  -/
lemma binop_eq_some_of_isIndependentProduct {p q r : PSpace α}
    (h : r =ᵢ p ⊕ᵢ q) : p ⋆ q = some r := by
  unfold instPcmBase;
  have h_unique : ∃! r, r =ᵢ p ⊕ᵢ q := by
    have := @PSpace.uniqueness α;
    exact ⟨r, h, fun r' hr' => this _ _ _ _ hr' h⟩;
  grind

/- If `p' =ᵢ x' ⊕ᵢ y'`, `x ≤ x'`, `y ≤ y'`, then the trim of `p'` to `x.ms.sum y.ms`
is an independent product of `x` and `y`.  -/
lemma trim_isIndependentProduct {x x' y y' p' : PSpace β}
    (x_le : x ≤ x') (y_le : y ≤ y') (h_p' : p' =ᵢ x' ⊕ᵢ y')
    (h_ms : x.1.ms.sum y.1.ms ≤ p'.1.ms) :
    (p'.trim h_ms) =ᵢ x ⊕ᵢ y := by
  constructor;
  · rfl;
  · intro E hE F hF;
    convert h_p'.2 E (x_le.1 _ hE) F (y_le.1 _ hF) using 1;
    · convert MeasureOnSpace.trim_eq h_ms _;
      exact mem_sum_inter x.ms y.ms hE hF;
    · rw [MeasureOnSpace.le_preserves_measure x_le hE, MeasureOnSpace.le_preserves_measure y_le hF]

def le_mul_mono (x x' y y' p' : PSpace α) (x_le : x ≤ x') (y_le : y ≤ y')
    (ex_ge_mul : x' ⋆ y' = some p') : ∃ p, (x ⋆ y = some p) ∧ p ≤ p' := by
  have h_p' : p' =ᵢ x' ⊕ᵢ y' := isIndependentProduct_of_binop_eq_some ex_ge_mul
  have h_ms : x.1.ms.sum y.1.ms ≤ p'.1.ms := by
    rw [h_p'.1]
    exact MeasurableSpace.sum_mono_both x_le.1 y_le.1
  let p := p'.trim h_ms
  have h_p : p =ᵢ x ⊕ᵢ y := trim_isIndependentProduct x_le y_le h_p' h_ms
  exact ⟨p, binop_eq_some_of_isIndependentProduct h_p, PSpace.trim_le h_ms⟩

noncomputable instance instKrm : Krm (PSpace α) where
  one_le _ := PSpace.le_of_isIndependentProduct_left PSpace.indepenendentProduct_identity
  le_mul_mono := le_mul_mono

end Krm
end PSpace

open HC

structure PSp extends (PSpace HC) where
  finite_footprint : ∃ n, FiniteFootprint n ms

/- This proof uses proof irrelevance in lean and shows that if in a subspace of a Krm,
the binary operation is closed, then the subspace is a KRM as well. -/
def closed_subtype_Krm (α : Type*) [Krm α] (β : Type*) [PcmBase β] (f : β → α)
    (f_inj : Function.Injective f)
    (f_one : f 1 = 1)
    (f_binop : ∀ x y : β, (x ⋆ y).map f = (f x) ⋆ (f y)) : Krm β where
  one_mul a := Option.map_injective f_inj <| by
    rw [Option.map_some, f_binop, f_one, Pcm.one_mul]
  comm a b := Option.map_injective f_inj <| by
    rw [f_binop, f_binop, Pcm.comm]
  assoc a b c := by
    apply Option.map_injective f_inj
    convert Pcm.assoc (f a) (f b) (f c) using 1
    · cases h : a ⋆ b <;> simp [← f_binop, h]; rfl
    · cases h : b ⋆ c <;> simp [← f_binop, h]; rfl
  le x y := f x ≤ f y
  le_refl x := le_refl (f x)
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  one_le a := f_one ▸ Krm.one_le (f a)
  le_mul_mono x x' y y' p' hx hy hp := by
    obtain ⟨q, hq, hqle⟩ := Krm.le_mul_mono (f x) (f x') (f y) (f y') (f p') hx hy
      (by rw [← f_binop, hp]; rfl)
    rw [← f_binop, Option.map_eq_some_iff] at hq
    obtain ⟨p, hp_xy, rfl⟩ := hq
    exact ⟨p, hp_xy, hqle⟩


namespace PSp
open Classical

prefix:max "✓'" => Option.isSome

abbrev coerceOption {α : Type*} {x : Option α} (h : x.isSome) := x.get h

prefix:max "↓" => coerceOption

lemma ff_closed_under_sum (ms₁ ms₂ : MeasurableSpace HC) (hms₁ : ∃ n, FiniteFootprint n ms₁)
    (hms₂ : ∃ n, FiniteFootprint n ms₂) : ∃ n, FiniteFootprint n (ms₁.sum ms₂) := by
  obtain ⟨n₁, ff₁⟩ := hms₁
  obtain ⟨n₂, ff₂⟩ := hms₂
  use max n₁ n₂
  obtain ⟨ms₁', hms₁⟩ := finite_footprint_of_ge (le_max_left n₁ n₂) ff₁
  obtain ⟨ms₂', hms₂⟩ := finite_footprint_of_ge (le_max_right n₁ n₂) ff₂
  use ms₁'.sum ms₂'
  simp_all only [unSplitBi_eq_comap_fst, sum]
  rw [comap_generateFrom, Set.image_union]
  congr 1

/-
The unit PSpace has finite footprint (trivial σ-algebra depends on 0 coordinates).
-/
lemma ff_unit : ∃ n, FiniteFootprint n (PSpace.unit (Ω := HC)).ms := by
  use 0, ⊥
  simp [PSpace.unit, unSplitBi_eq_comap_fst]

noncomputable instance : One PSp where
  one := ⟨PSpace.unit, ff_unit⟩

/-- If `r =ᵢ p ⊕ᵢ q` and both `p` and `q` have finite footprint, then `r` does too. -/
lemma ff_of_isIndependentProduct {p q r : PSpace HC}
    (h : r =ᵢ p ⊕ᵢ q) (hp : ∃ n, FiniteFootprint n p.ms) (hq : ∃ n, FiniteFootprint n q.ms) :
    ∃ n, FiniteFootprint n r.ms := by
  rw [h.1]
  exact ff_closed_under_sum p.ms q.ms hp hq

noncomputable instance instPcmBase : PcmBase (PSp) where
  binop p q := if h: ∃! r, r =ᵢ p.1 ⊕ᵢ q.1 then
    some ⟨h.choose, ff_of_isIndependentProduct h.choose_spec.1 p.2 q.2⟩
  else none

/-- The map `PSp → PSpace HC` given by `Subtype.val` preserves the unit. -/
lemma psp_val_one : (1 : PSp).1 = (1 : PSpace HC) := rfl

/- The map `PSp → PSpace HC` given by `Subtype.val` preserves `binop` values.  -/
lemma psp_val_binop (x y : PSp) : (x ⋆ y).map (·.1) = (x.1 ⋆ y.1) := by
  rw [instPcmBase, PSpace.instPcmBase]
  grind

/-- PSp is a Krm using `closed_subtype_Krm`. -/
noncomputable instance instKrm : Krm PSp := closed_subtype_Krm (PSpace HC) PSp (·.1)
  (by rintro ⟨a, ha⟩ ⟨b, hb⟩ c; simpa only [mk.injEq])
  rfl
  psp_val_binop

@[simp]
lemma le_of_le {x y : PSp} (x_le_y : x ≤ y) : x.ms ≤ y.ms := x_le_y.1


/-- The PSpace-level binop is also defined when the PSp binop is. -/
lemma psp_isSome_val (x y : PSp) (h : ✓'(x ⋆ y)) : ✓'(x.1 ⋆ y.1) := by
  have hv := psp_val_binop x y
  cases hxy : x ⋆ y with
  | none => simp [hxy] at h
  | some v =>
    simp only [hxy, Option.map_some] at hv
    rw [← hv]
    rfl

/- If PSp binop is defined, the underlying PSpace value equals the PSpace-level binop value.  -/
lemma psp_val_get (x y : PSp) (h : ✓'(x ⋆ y)) :
    (↓h).1 = ↓(psp_isSome_val x y h) := by
      convert Option.some_inj.mp _;
      convert psp_val_binop x y using 1;
      · unfold instPcmBase;
        grind;
      · grind

@[simp]
lemma sum_ms_of_prod {x y : PSp} (xy : ✓'(x ⋆ y)) : (↓xy).ms = x.ms.sum y.ms := by
  have hval : x.1 ⋆ y.1 = some (↓xy).1 := by
    rw [psp_val_get x y xy, Option.some_get]
  exact (PSpace.Krm.isIndependentProduct_of_binop_eq_some hval).1


open MeasureTheory in
noncomputable def PSpace.mk''_psp {ms ms' : MeasurableSpace HC} (μ : @ProbabilityMeasure HC ms)
    (ms'_le_ms : ms' ≤ ms) (ff : ∃ n, FiniteFootprint n ms') : PSp :=
  ⟨⟨⟨ms', μ.1.trim ms'_le_ms⟩, Measure.trim_preserves_prob ms' ms ms'_le_ms μ.2⟩, ff⟩

end PSp

/- Helper functions which re-interpret the Krm laws in terms of the `Option.is_some` and
`Option.get` API, introduced using the notation `✓'` and `↓`. -/
namespace Krm

variable {α : Type*} [krm_α : Krm α]
open PcmBase

/-- If `a ⋆ b = b ⋆ a`, then `Option.get` yields equal values. -/
lemma get_comm (a b : α) (hab : ✓'(a ⋆ b)) (hba : ✓'(b ⋆ a)) :
    ↓hab = ↓hba := by
  have h : a ⋆ b = b ⋆ a := Pcm.comm a b
  set x := (a ⋆ b).get hab
  set y := (b ⋆ a).get hba
  have hax : a ⋆ b = some x := Option.some_get hab ▸ rfl
  have hay : b ⋆ a = some y := Option.some_get hba ▸ rfl
  exact Option.some_injective _ (hax.symm.trans (h.trans hay))

lemma right {a b c : α}
    {hab : ✓'(a ⋆ b)} (habc : ✓'(↓hab ⋆ c)) :
    ✓'(b ⋆ c) := by
      have assoc_lhs: ((krm_α.binop) <$> (a ⋆ b) <*> (some c)).join = (↓hab ⋆ c) := by
        conv_lhs => rw [← Option.some_get hab]
        rfl
      have assoc := assoc_lhs ▸ krm_α.assoc a b c
      rw [assoc] at habc
      by_cases h: ✓'(b ⋆ c)
      · exact h
      · exfalso
        have : b ⋆ c = none := by exact Option.not_isSome_iff_eq_none.mp h
        rw [this] at habc
        contradiction

lemma left {a b c : α}
    {hbc : ✓'(b ⋆ c)} (habc : ✓'(a ⋆ ↓hbc)) :
    ✓'(a ⋆ b) := by
      have assoc_rhs: (binop <$> (some a) <*> (b ⋆ c)).join = (a ⋆ ↓hbc) := by
        conv_lhs => rw [← Option.some_get hbc]
        rfl
      have assoc := assoc_rhs ▸ krm_α.assoc a b c
      rw [← assoc] at habc
      by_cases h: ✓'(a ⋆ b)
      · exact h
      · exfalso
        have : a ⋆ b = none := by exact Option.not_isSome_iff_eq_none.mp h
        rw [this] at habc
        contradiction

/- Given `↓hab ⋆ c` is defined, so is `a ⋆ ↓hbc`.  -/
lemma assoc_right {a b c : α} {hab : ✓'(a ⋆ b)} (habc : ✓'(↓hab ⋆ c)) :
  ✓'(a ⋆ ↓(right habc)) := by
    have hassoc := ‹Krm α›.assoc a b c
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hab
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp habc
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp <| right habc
    simp_all

/- Given `a ⋆ ↓hbc` is defined, so is `↓hab ⋆ c`.  -/
lemma assoc_left {a b c : α} {hbc : ✓'(b ⋆ c)} (habc : ✓'(a ⋆ ↓hbc)) :
  ✓'(↓(left habc) ⋆ c) := by
    have hassoc := ‹Krm α›.assoc a b c
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp <| left habc
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp habc
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hbc
    simp_all

/-- The result of reassociating `(a ⋆ b) ⋆ c` to `a ⋆ (b ⋆ c)` via `assoc_left`
yields the same combined element. -/
@[simp]
lemma assoc_left_eq {a b c : α} {hbc : ✓'(b ⋆ c)} (habc : ✓'(a ⋆ ↓hbc)) :
    ↓(assoc_left habc) = ↓habc := by
  apply Option.some_injective
  rw [Option.some_get, Option.some_get]
  have hassoc := krm_α.assoc a b c
  conv at hassoc =>
    lhs; rw [show a ⋆ b = some (↓(left habc)) from (Option.some_get _).symm]
  conv at hassoc =>
    rhs; rw [show b ⋆ c = some (↓hbc) from (Option.some_get _).symm]
  convert hassoc using 1

/-- The result of reassociating `a ⋆ (b ⋆ c)` to `(a ⋆ b) ⋆ c` via `assoc_right`
yields the same combined element. -/
@[simp]
lemma assoc_right_eq {a b c : α} {hab : ✓'(a ⋆ b)} (habc : ✓'(↓hab ⋆ c)) :
    ↓(assoc_right habc) = ↓habc := by
  apply Option.some_injective
  rw [Option.some_get, Option.some_get]
  have hassoc := krm_α.assoc a b c
  conv at hassoc =>
    lhs; rw [show a ⋆ b = some (↓hab) from (Option.some_get _).symm]
  conv at hassoc =>
    rhs; rw [show b ⋆ c = some (↓(right habc)) from (Option.some_get _).symm]
  convert hassoc.symm using 1

lemma le_mul_mono' (x₁ x₂ y₁ y₂ : α)
    (lex : x₁ ≤ x₂) (ley : y₁ ≤ y₂)
    (xy₂ : ✓'(x₂ ⋆ y₂)) : ∃ xy₁ : ✓'(x₁ ⋆ y₁), ↓xy₁ ≤ ↓xy₂ := by
  obtain ⟨p, hp, hple⟩ := krm_α.le_mul_mono x₁ x₂ y₁ y₂ (↓xy₂) lex ley (Option.some_get xy₂).symm
  exact ⟨hp ▸ rfl, by simp only [hp, Option.get_some]; exact hple⟩

lemma le_mul_mono_left' {x₁ x₂ y : α} (lex : x₁ ≤ x₂) (xy₂ : ✓'(x₂ ⋆ y)) :
  ∃ xy₁ : ✓'(x₁ ⋆ y), ↓xy₁ ≤ ↓xy₂ := le_mul_mono' x₁ x₂ y y lex (le_refl y) xy₂

lemma le_mul_mono_right' {x y₁ y₂ : α} (ley : y₁ ≤ y₂) (xy₂ : ✓'(x ⋆ y₂)) :
  ∃ xy₁ : ✓'(x ⋆ y₁), ↓xy₁ ≤ ↓xy₂ := le_mul_mono' x x y₁ y₂ (le_refl x) ley xy₂

end Krm
