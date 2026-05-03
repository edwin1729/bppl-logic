/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Iris.BI.Extensions
import Iris.Std.Equivalence

import Bppl.Lilac.KRM

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
This file instantiates MoSeL (the Iris frontend) to obtain an intuitionistic separation logic
from a KRM (Kripke Resource Monoid).
-/

namespace Iris.Instances.Intuitionistic

open Iris.BI

variable {Env Resource : Type*} [Krm Resource]

/-- An "Iris Proposition" (prop in the separation logic) is defined by this deep embedding,
directly providing the semantics.
In this subtype the data part, `sem`, defines the satisfiability relation, and we add the
monotonicity constraint: any `IProp` satisfied by a "less informative" resource is also satisfied
by a more informative resource. -/
abbrev IProp (Resource : Type*) [Krm Resource]
  := {sem : Resource → Prop // ∀ σ₁ σ₂, σ₁ ≤ σ₂ → sem σ₁ → sem σ₂}

/-! ### BIBase instance -/

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
      obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono σP σP σ₁ σ₂ ((σP ⋆ σ₂).get σQ)
        (Preorder.le_refl σP) σ₁_le_σ₂ ((Option.some_get σQ).symm)
      have hs : (σP ⋆ σ₁).isSome = true := hp.symm ▸ rfl
      have hle : (σP ⋆ σ₁).get hs ≤ (σP ⋆ σ₂).get σQ := by
        simp only [← hp.symm, Option.get_some]; exact hple
      exact Q.2 _ _ hle (h σP hs hP)
    ⟩
  persistently P := ⟨fun _ ↦ P.1 1, fun _ _ _ h ↦ h⟩
  later P        := ⟨fun σ ↦ P.1 σ, P.2⟩

instance : Std.Preorder (Entails (PROP := IProp Resource)) where
  refl := fun _ h => h
  trans := fun h_xy h_yz σ h_x => h_yz σ (h_xy σ h_x)

instance : COFE (IProp Resource) :=
  COFE.ofDiscrete Eq equivalence_eq

/-! ### BI instance -/
open BI in
/-- These proofs have been ported from the Iris-lean to the classical separation logic,
modified as necessary. -/
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

  and_elim_l := by dsimp only [Entails, BI.and]; tauto
  and_elim_r := by dsimp only [Entails, BI.and]; tauto
  and_intro := by dsimp only [Entails, BI.and]; tauto

  or_intro_l := by dsimp only [Entails, BI.or]; tauto
  or_intro_r := by dsimp only [Entails, BI.or]; tauto
  or_elim := by dsimp only [Entails, BI.or]; tauto

  imp_intro := by dsimp only [Entails, BI.imp, BI.and]; grind
  imp_elim := by
    dsimp only [Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    exact h_PQR σ h_P σ (Preorder.le_refl σ) h_Q

  sForall_intro := by
    dsimp only [Entails]
    intro _ _ h_PΨ σ h_P p hp
    exact h_PΨ p hp σ h_P
  sForall_elim := by
    simp only [Entails]
    intro _ _ hp _ h_Ψ
    exact h_Ψ _ hp

  sExists_intro := by
    simp only [Entails]
    intro _ _ hp _ h_Ψ
    exact ⟨_, hp, h_Ψ⟩
  sExists_elim := by
    simp only [Entails]
    intro _ _ h_ΦQ σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp σ h_Φ

  sep_mono := by dsimp only [Entails, sep]; tauto
  emp_sep := ⟨
    fun σ h => by
      rename_i P
      obtain ⟨σ₁, σ₂, h_s, h_le, _, hP⟩ := h
      obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono 1 σ₁ σ₂ σ₂ ((σ₁ ⋆ σ₂).get h_s)
        (Krm.one_le σ₁) (Preorder.le_refl σ₂) ((Option.some_get h_s).symm)
      have : p = σ₂ := Option.some_injective _ ((Pcm.one_mul σ₂).symm ▸ hp.symm)
      exact P.2 σ₂ σ (this ▸ hple |>.trans h_le) hP,
    fun σ hP => ⟨1, σ, by rw [Pcm.one_mul]; rfl, by simp [Pcm.one_mul], trivial, hP⟩⟩
  sep_symm := fun σ h => by
    obtain ⟨σ₁, σ₂, s, h_le, hP, hQ⟩ := h
    exact ⟨σ₂, σ₁, Pcm.comm σ₂ σ₁ ▸ s, by simp only [Pcm.comm σ₂ σ₁]; exact h_le, hQ, hP⟩
  sep_assoc_l := fun σ h => by
    obtain ⟨σ₁₂, σ₃, s₁₂₃, h_le₁₂₃, ⟨σ₁, σ₂, s₁₂, h_le₁₂, hP, hQ⟩, hR⟩ := h
    obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono ((σ₁ ⋆ σ₂).get s₁₂) σ₁₂ σ₃ σ₃
      ((σ₁₂ ⋆ σ₃).get s₁₂₃) h_le₁₂ (Preorder.le_refl σ₃) ((Option.some_get s₁₂₃).symm)
    have lhs : (PcmBase.binop <$> (σ₁ ⋆ σ₂) <*> some σ₃).join = some p := by
      rw [(Option.some_get s₁₂).symm]; change ((σ₁ ⋆ σ₂).get s₁₂) ⋆ σ₃ = some p; exact hp
    rw [Pcm.assoc] at lhs
    obtain ⟨bc, hbc, habc⟩ : ∃ bc, σ₂ ⋆ σ₃ = some bc ∧ σ₁ ⋆ bc = some p := by
      cases hbc : σ₂ ⋆ σ₃ with
      | none => rw [hbc] at lhs; cases lhs
      | some bc => rw [hbc] at lhs; change (σ₁ ⋆ bc) = some p at lhs; exact ⟨bc, rfl, lhs⟩
    refine ⟨σ₁, bc, habc.symm ▸ rfl, ?_, hP, σ₂, σ₃, hbc.symm ▸ rfl, ?_, hQ, hR⟩
    · change (σ₁ ⋆ bc).get (habc.symm ▸ rfl) ≤ σ
      have : (σ₁ ⋆ bc).get (habc.symm ▸ rfl) = p := by simp [habc]
      rw [this]; exact hple.trans h_le₁₂₃
    · change (σ₂ ⋆ σ₃).get (hbc.symm ▸ rfl) ≤ bc
      have : (σ₂ ⋆ σ₃).get (hbc.symm ▸ rfl) = bc := by simp [hbc]
      rw [this]

  wand_intro := fun h σ hP σQ h_s hQ => by
    apply h
    exact ⟨σ, σQ, Pcm.comm σ σQ ▸ h_s,
      by simp only [Pcm.comm σ σQ]; exact Preorder.le_refl _, hP, hQ⟩
  wand_elim := fun h σ hex => by
    rename_i _ _ R
    obtain ⟨σ₁, σ₂, s, h_le, hP, hQ⟩ := hex
    have hr := h σ₁ hP σ₂ (Pcm.comm σ₂ σ₁ ▸ s) hQ
    simp only [Pcm.comm σ₂ σ₁] at hr
    exact R.2 _ σ h_le hr

  persistently_mono := by dsimp only [Entails, persistently]; tauto
  persistently_idem_2 := by dsimp only [Entails, persistently]; intro _ _ h; exact h
  persistently_emp_2 := by dsimp only [Entails, persistently, emp]; intro σ P; trivial
  persistently_and_2 := by dsimp only [Entails, persistently, BI.and]; intro _ _ _ h; exact h
  persistently_sExists_1 := by
    dsimp only [Entails, persistently, BI.exists]
    intro _ σ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by dsimp only [Entails, persistently, sep]; grind
  persistently_and_l := fun σ h => by
    refine ⟨1, σ, ?_, ?_, h.1, h.2⟩
    · rw [Pcm.one_mul]; rfl
    · simp [Pcm.one_mul]

  later_mono := id
  later_intro _ := id
  later_sForall_2 := by
    dsimp only [Entails, BI.pure, BI.imp, later, sForall]
    intro Φ σ h p hp
    have := h ⟨fun σ ↦ ∀ σ', σ ≤ σ' → Φ p → p.1 σ',
      fun σ₁ σ₂ h₁₂ h₁ σ' h₂ ↦ h₁ σ' (h₁₂.trans h₂)⟩ ⟨_, rfl⟩
    exact this σ (Preorder.le_refl σ) hp
  later_sExists_false := by
    dsimp only [Entails, later, BI.or, BI.exists, BI.pure]
    intro _ _ ⟨p, hp⟩
    exact Or.inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ => id, fun _ => id⟩
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em := by dsimp only [Entails, later, BI.or, BI.imp, BI.pure]; grind

-- Intuitionistic is supposed to mean a proposition can be freely duplicated or dropped,
-- ie, persistent + affine (according to the MoSeL paper).

-- But my understanding of what the ordering relation in a KRM allows is
-- `Affine` not `Intuitionistic`. Clear up this confusion and clarify the
-- terminology for the report.

-- For now I assume:

/-- A KRM generates a separation logic where every proposition is
affine (may be dropped in a proof).
NB: This instance is **incorrect** in general and is left as `sorry`. -/
instance KRM_BIAffine : BIAffine (IProp Resource) where
  affine P := sorry

end Iris.Instances.Intuitionistic
