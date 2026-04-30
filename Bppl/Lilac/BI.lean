/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence
import Mathlib.Order.WithBot

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
This file instantiates MoSeL (the Iris frontend) to obtain an intuitionistic separation logic
from a KRM (Kripke Resource Monoid).
-/

namespace Iris.Instances.Intuitionistic

-- open WithBot
open Iris.BI

variable {Env Resource : Type*} [Krm Resource]

/-- An "Iris Proposition" (prop in the separation logic) is defined by this deep embedding,
directly providing the semantics.
In this subtype the data part, `sem`, defines the satisfiability relation, and we add the
monotonicity constraint: any `IProp` satisfied by a "less informative" resource is also satisfied
by a more informative resource.
The `Env` is modelled as a single type, so if we need a deterministic and random environment,
it needs to be expressed as a tuple. -/
abbrev IProp (Resource : Type*) [Krm Resource]
  := {sem : Resource → Prop // ∀ σ₁ σ₂, σ₁ ≤ σ₂ → sem σ₁ → sem σ₂}

prefix:max "✓'" => Option.isSome

abbrev foo {x : Option α} (h : x.isSome) := x.get h

prefix:max "↓" => foo

theorem Krm.le_mul_mono' {α : Type*} [k : Krm α] (x x' y y' : α) :
    (∀ p' : α, x ≤ x' → y ≤ y' →
    (some p' = x' ⋆ y') → ∃ p, (some p = x ⋆ y) ∧ p ≤ p')
    ↔
    (x ≤ x' → y ≤ y' →
    ∀ p' : ✓'(x' ⋆ y'), ∃ p: ✓'(x ⋆ y), ↓p ≤ ↓p') := by
  constructor
  ·
    intro h x_le y_le p'
    have ⟨p, hp, p_le_p'⟩ := h ↓p' x_le y_le (Option.some_get p')
    use hp ▸ @Option.isSome_some _ p
    trans p
    ·
      apply le_of_eq
      rw [foo]
      -- nth_rewrite 1 [← hp]

      -- exact (Option.get_some p (hp ▸ Option.isSome_some))
      sorry
    · exact p_le_p'

  · sorry



-- instance {α : Type*} {x : Option α} : Coe (x.isSome = true) α where
--   coe (h : x.isSome = true) := x.get h

instance instBIBase : BIBase (IProp Resource) where
  Entails P Q    := ∀ σ, P.1 σ → Q.1 σ
  emp            := ⟨fun _ ↦ True, fun _ _ _ _ ↦ trivial⟩
  pure φ         := ⟨fun _ ↦ φ, fun _ _ _ hσ₁ ↦ hσ₁⟩
  and P Q        := ⟨fun σ ↦ P.1 σ ∧ Q.1 σ, by
    intro σ₁ σ₂ hle ⟨hPσ₁, hQσ₁⟩
    exact ⟨P.2 σ₁ σ₂ hle hPσ₁ , Q.2 σ₁ σ₂ hle hQσ₁⟩
  ⟩
  or P Q        := ⟨fun σ ↦ P.1 σ ∨ Q.1 σ,
    fun σ1 σ2 hle hσ1 => hσ1.elim (Or.inl ∘ P.2 σ1 σ2 hle) (Or.inr ∘ Q.2 σ1 σ2 hle)
  ⟩
  imp P Q        := ⟨fun σ ↦ ∀ σ', σ ≤ σ' → (P.1 σ' → Q.1 σ'),
    fun σ₁ σ₂ σ₁_le_σ₂ hσ₁ σ' σ₂_le_σ' hPσ' ↦ hσ₁ σ' (σ₁_le_σ₂.trans σ₂_le_σ') hPσ'
  ⟩
  -- The idea ito get a singleton set of a ∀ or ∀ᵣᵥ assertion ainput and the same term
  -- aoutput (when taking denotation). So the dand rtype indiceare the same
  sForall Ψ      := ⟨fun σ ↦ ∀ p, Ψ p → p.1 σ, by
    intro σ₁ σ₂ σ₁_le_σ₂ hσ₁ p hp
    exact p.2 σ₁ σ₂ σ₁_le_σ₂ (hσ₁ p hp)
  ⟩
  sExists Ψ      := ⟨fun σ ↦ ∃ p, Ψ p ∧ p.1 σ, by
    intro σ₁ σ₂ σ₁_le_σ₂ ⟨p, hp, hpσ₁⟩
    exact ⟨p, hp, p.2 σ₁ σ₂ σ₁_le_σ₂ hpσ₁⟩
  ⟩
  sep P Q        :=
    ⟨fun σ ↦ ∃ σ₁ σ₂, ∃ (σ₁₂ : ✓'(σ₁ ⋆ σ₂)), ↓σ₁₂ ≤ σ ∧ P.1 σ₁ ∧ Q.1 σ₂,
    by
      intro σ₁ σ₂ σ₁_le_σ₂ ⟨σP, σQ, h_exists, h_le, hP, hQ⟩
      use σP, σQ, h_exists
      exact ⟨h_le.trans σ₁_le_σ₂, hP, hQ⟩
    ⟩
  wand P Q       := ⟨fun σ ↦ ∀ σP, ∀ σQ : ✓'(σP ⋆ σ), (P.1 σP → Q.1 ↓σQ), by
      intro σ₁ σ₂ σ₁_le_σ₂ h σP σQ hP

      sorry
      -- exact h σP σQ hP
    ⟩
  persistently P := ⟨fun σ ↦ P.1 1, sorry⟩
  later P        := ⟨fun σ ↦ P.1 σ, sorry⟩

instance : Std.Preorder (Entails (PROP := IProp Resource)) where
  refl := by
    simp only [BI.Entails]
    intro _ _ h
    exact h
  trans := by
    simp only [BI.Entails]
    intro _ _ _ h_xy h_yz σ h_x
    apply h_yz σ
    apply h_xy σ
    exact h_x

instance : COFE (IProp Resource) :=
  COFE.ofDiscrete Eq equivalence_eq

/-- These proofhave been ported from the Iris-lean to the classical separation logic,
modified anecessary. The similaritiebetween the two logicithe lack of step-indexing
and general similarity in non-spatial axiom -/
instance instBI : BI (IProp Resource) where
  entails_preorder := by infer_instance
  equiv_iff {P Q} := ⟨
    fun h : P = Q => h ▸ ⟨fun _ φ ↦ φ, fun _ φ ↦ φ⟩,
    fun ⟨h₁, h₂⟩ => by ext σ; exact ⟨h₁ σ, h₂ σ⟩
  ⟩
  and_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  or_ne           := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  imp_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  sep_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  wand_ne         := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  persistently_ne := ⟨by rintro _ _ _ rfl; rfl⟩
  later_ne        := ⟨by rintro _ _ _ rfl; rfl⟩
  sForall_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl
  sExists_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl

  pure_intro h _ _ := h
  pure_elim' h_φP σ h_φ := h_φP h_φ σ ⟨⟩

  and_elim_l := by
    intros
    simp only [BI.Entails, BI.and]
    intro _ h
    exact h.left
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h
    exact h.right
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR σ h_P
    constructor
    · exact h_PQ σ h_P
    · exact h_PR σ h_P

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR σ h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR σ h_P
    case inr h_Q =>
      exact h_QR σ h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ h_P Ω' Ω_le_Ω' h_Q
    sorry -- TODO ≤ (actually the below case ithe problem)
    -- exact h_PQR σ ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    sorry -- TODO ≤
    -- exact h_PQR σ h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ σ h_P p hp
    exact h_PΨ p hp σ h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact ⟨p, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp σ h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ h_PQ h_P'Q' σ ⟨σ₁, σ₂, h_Ω, h_P, h_P'⟩
    use σ₁, σ₂
    sorry
    -- exact ⟨h_Ω, h_PQ σ₁ h_P, h_P'Q' σ₂ h_P'⟩
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp]

    intro _ ⟨σ₁, σ₂, h_Ω, h_emp, h_P⟩
    --
    -- rw [h_emp] at h_union
    -- rw [h_emp, Pcm.one_mul, Option.some_le_some] at h_Ω
    sorry -- TODO ≤
    -- rw [← h_Ω]
    -- exact h_Ω ▸ h_P
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp]
    sorry -- TODO ≤ (Thiiactually provable. Just inverse of the above broken case
    -- so skipped)
  sep_symm := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ ⟨σ₁, σ₂, h_union, h_P, h_Q⟩
    use σ₂, σ₁
    rw [Pcm.comm]
    sorry
    -- exact ⟨h_union, h_Q, h_P⟩
  sep_assoc_l := by
    simp only [BI.Entails, BI.sep]
    -- intro _ _ _ _ _ ⟨Ω₁₂, Ω₃, h_Ω₁₂₃ₗ, ⟨Ω₁, Ω₂, h_Ω₁₂, h_P₁, h_P₂⟩, h_P₃⟩
    -- use Ω₁
    -- usage of Pcm.assoc iobstructed by ≤
    sorry  -- Todo ≤

  -- suspect these might change due to ≤
  wand_intro := sorry
  wand_elim := sorry

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ _ h_P
    exact h_PQ 1 h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro σ P
    trivial
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ h
    exact h
  persistently_sExists_1 := by
    simp only [BI.Entails, BI.persistently, BI.exists]
    intro _ _ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ _ ⟨_, _, _, h_P, _⟩
    sorry
    -- exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
    intro _ _ σ ⟨h_P, h_Q⟩
    apply Exists.intro 1
    apply Exists.intro σ
    sorry
    -- constructor
    -- · rw [Pcm.one_mul, Option.some_le_some]
    -- constructor
    -- · exact h_P
    -- · exact h_Q

  later_mono := id
  later_intro _ := id
  later_sForall_2 {Φ} σ P := by
    simp only [later, sForall] -- for clarity, can delete
    intro Q h_Q
    let foo := P Q
    apply foo
    use Q
    simp [BI.pure, later]
    ext σ
    constructor
    ·
      intro P'
      exact P' σ (le_refl _) h_Q
    ·
      intro q Ω' h_Ω' P'
      sorry -- TODO ≤ (require that bigger )

  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ => id, fun _ => id⟩
  later_persistently := ⟨fun _ => id, fun  _ => id⟩
  later_false_em _ h := .inr fun _ _ => (by
    simp [later] at h
    sorry -- TODO ≤ :(
    -- exact h
  )

-- Intuitionistic is supposed to mean a proposition can be freely duplicated or dropped,
-- ie, persistent + affine (according to the MoSeL paper).

-- But my understanding of what the ordering relation in a KRM allows is
-- `Affine` not `Intuitionistic`. Clear up this confusion and clarify the
-- terminology for the report.

-- For now I assume:

/-- A KRM generates a separation logic where every proposition is
affine (may be dropped in a proof) -/
instance KRM_BIAffine : BIAffine (IProp Resource) where
  affine P := sorry

end Iris.Instances.Intuitionistic
