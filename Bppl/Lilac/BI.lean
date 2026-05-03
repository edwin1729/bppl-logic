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
import Mathlib

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl

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
by a more informative resource.
The `Env` is modelled as a single type, so if we need a deterministic and random environment,
it needs to be expressed as a tuple. -/
abbrev IProp (Resource : Type*) [Krm Resource]
  := {sem : Resource → Prop // ∀ σ₁ σ₂, σ₁ ≤ σ₂ → sem σ₁ → sem σ₂}

/-! ### Helper lemmas for Option.get / isSome manipulation -/

private lemma isSome_of_eq_some' {x : Option α} {a : α} (h : some a = x) :
    x.isSome = true := by subst h; rfl

private lemma get_eq_of_eq_some' {x : Option α} {a : α} (h : some a = x)
    (hs : x.isSome = true) : x.get hs = a := by subst h; rfl

/-! ### Krm.le_mul_mono' -/

theorem Krm.le_mul_mono' {α : Type*} [k : Krm α] (x x' y y' : α) :
    (∀ p' : α, x ≤ x' → y ≤ y' →
    (some p' = x' ⋆ y') → ∃ p, (some p = x ⋆ y) ∧ p ≤ p')
    ↔
    (x ≤ x' → y ≤ y' →
    ∀ p' : ✓'(x' ⋆ y'), ∃ p: ✓'(x ⋆ y), ↓p ≤ ↓p') := by
  constructor
  · intro h hx hy p'
    obtain ⟨p, hp, hple⟩ := h ((x' ⋆ y').get p') hx hy (Option.some_get p')
    exact ⟨hp ▸ rfl, by simp only [← hp, Option.get_some]; exact hple⟩
  · intro h p' hx hy hp'
    obtain ⟨q, hq⟩ := h hx hy (hp' ▸ rfl)
    exact ⟨(x ⋆ y).get q, Option.some_get q, by convert hq using 1; simp [← hp', Option.get_some]⟩

/-! ### Auxiliary lemma for wand monotonicity -/

private lemma krm_wand_mono [Krm α] {σ₁ σ₂ σP : α}
    (hle : σ₁ ≤ σ₂) (hsome : (σP ⋆ σ₂).isSome = true) :
    ∃ (hs : (σP ⋆ σ₁).isSome = true), (σP ⋆ σ₁).get hs ≤ (σP ⋆ σ₂).get hsome := by
  obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono σP σP σ₁ σ₂ ((σP ⋆ σ₂).get hsome)
    (Preorder.le_refl σP) hle ((Option.some_get hsome).symm)
  exact ⟨hp.symm ▸ rfl, by simp only [← hp.symm, Option.get_some]; exact hple⟩

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
      obtain ⟨hs, hle⟩ := krm_wand_mono σ₁_le_σ₂ σQ
      exact Q.2 _ _ hle (h σP hs hP)
    ⟩
  persistently P := ⟨fun _ ↦ P.1 1, fun _ _ _ h ↦ h⟩
  later P        := ⟨fun σ ↦ P.1 σ, P.2⟩

instance : Std.Preorder (Entails (PROP := IProp Resource)) where
  refl := fun _ h => h
  trans := fun h_xy h_yz σ h_x => h_yz σ (h_xy σ h_x)

instance : COFE (IProp Resource) :=
  COFE.ofDiscrete Eq equivalence_eq

/-! ### Helper lemmas for BI axioms -/

private lemma emp_sep_mp {P : IProp Resource}
    (σ : Resource)
    (h : ∃ σ₁ σ₂, ∃ (σ₁₂ : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get σ₁₂ ≤ σ ∧ True ∧ P.1 σ₂) :
    P.1 σ := by
  obtain ⟨σ₁, σ₂, h_s, h_le, _, hP⟩ := h
  obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono 1 σ₁ σ₂ σ₂ ((σ₁ ⋆ σ₂).get h_s)
    (Krm.one_le σ₁) (Preorder.le_refl σ₂) ((Option.some_get h_s).symm)
  have : p = σ₂ := Option.some_injective _ ((Pcm.one_mul σ₂).symm ▸ hp.symm)
  exact P.2 σ₂ σ (this ▸ hple |>.trans h_le) hP

private lemma emp_sep_mpr {P : IProp Resource}
    (σ : Resource)
    (hP : P.1 σ) :
    ∃ σ₁ σ₂, ∃ (σ₁₂ : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get σ₁₂ ≤ σ ∧ True ∧ P.1 σ₂ := by
  refine ⟨1, σ, ?_, ?_, trivial, hP⟩
  · rw [Pcm.one_mul]; rfl
  · simp [Pcm.one_mul]

private lemma sep_symm_lem {P Q : IProp Resource}
    (σ : Resource)
    (h : ∃ σ₁ σ₂, ∃ (s : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get s ≤ σ ∧ P.1 σ₁ ∧ Q.1 σ₂) :
    ∃ σ₁ σ₂, ∃ (s : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get s ≤ σ ∧ Q.1 σ₁ ∧ P.1 σ₂ := by
  obtain ⟨σ₁, σ₂, s, h_le, hP, hQ⟩ := h
  exact ⟨σ₂, σ₁, Pcm.comm σ₂ σ₁ ▸ s, by simp only [Pcm.comm σ₂ σ₁]; exact h_le, hQ, hP⟩

private lemma assoc_rhs_some {a b c abc : Resource}
    (hassoc : (PcmBase.binop <$> some a <*> (b ⋆ c)).join = some abc) :
    ∃ bc, b ⋆ c = some bc ∧ a ⋆ bc = some abc := by
  cases hbc : b ⋆ c with
  | none => rw [hbc] at hassoc; cases hassoc
  | some bc => rw [hbc] at hassoc; change (a ⋆ bc) = some abc at hassoc; exact ⟨bc, rfl, hassoc⟩

private lemma sep_assoc_lem {P Q R : IProp Resource}
    (σ : Resource)
    (h : ∃ σ₁₂ σ₃, ∃ (s : (σ₁₂ ⋆ σ₃).isSome = true),
      (σ₁₂ ⋆ σ₃).get s ≤ σ ∧
      (∃ σ₁ σ₂, ∃ (s₁₂ : (σ₁ ⋆ σ₂).isSome = true),
        (σ₁ ⋆ σ₂).get s₁₂ ≤ σ₁₂ ∧ P.1 σ₁ ∧ Q.1 σ₂) ∧ R.1 σ₃) :
    ∃ σ₁ σ₂₃, ∃ (s : (σ₁ ⋆ σ₂₃).isSome = true),
      (σ₁ ⋆ σ₂₃).get s ≤ σ ∧ P.1 σ₁ ∧
      (∃ σ₂ σ₃, ∃ (s₂₃ : (σ₂ ⋆ σ₃).isSome = true),
        (σ₂ ⋆ σ₃).get s₂₃ ≤ σ₂₃ ∧ Q.1 σ₂ ∧ R.1 σ₃) := by
  obtain ⟨σ₁₂, σ₃, s₁₂₃, h_le₁₂₃, ⟨σ₁, σ₂, s₁₂, h_le₁₂, hP, hQ⟩, hR⟩ := h
  obtain ⟨p, hp, hple⟩ := Krm.le_mul_mono ((σ₁ ⋆ σ₂).get s₁₂) σ₁₂ σ₃ σ₃
    ((σ₁₂ ⋆ σ₃).get s₁₂₃) h_le₁₂ (Preorder.le_refl σ₃) ((Option.some_get s₁₂₃).symm)
  have lhs : (PcmBase.binop <$> (σ₁ ⋆ σ₂) <*> some σ₃).join = some p := by
    rw [(Option.some_get s₁₂).symm]; change ((σ₁ ⋆ σ₂).get s₁₂) ⋆ σ₃ = some p; exact hp
  rw [Pcm.assoc] at lhs
  obtain ⟨bc, hbc, habc⟩ := assoc_rhs_some lhs
  refine ⟨σ₁, bc, habc.symm ▸ rfl, ?_, hP, σ₂, σ₃, hbc.symm ▸ rfl, ?_, hQ, hR⟩
  · have : (σ₁ ⋆ bc).get (habc.symm ▸ rfl) = p := by simp [habc]
    rw [this]; exact hple.trans h_le₁₂₃
  · have : (σ₂ ⋆ σ₃).get (hbc.symm ▸ rfl) = bc := by simp [hbc]
    rw [this]

private lemma wand_intro_lem {P Q R : IProp Resource}
    (h : ∀ σ, (∃ σ₁ σ₂, ∃ (s : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get s ≤ σ ∧ P.1 σ₁ ∧ Q.1 σ₂) → R.1 σ)
    (σ : Resource)
    (hP : P.1 σ)
    (σQ : Resource)
    (h_s : (σQ ⋆ σ).isSome = true)
    (hQ : Q.1 σQ) :
    R.1 ((σQ ⋆ σ).get h_s) := by
  apply h
  exact ⟨σ, σQ, Pcm.comm σ σQ ▸ h_s,
    by simp only [Pcm.comm σ σQ]; exact Preorder.le_refl _, hP, hQ⟩

private lemma wand_elim_lem {P Q R : IProp Resource}
    (h : ∀ σ, P.1 σ → ∀ σQ, ∀ (s : (σQ ⋆ σ).isSome = true),
      Q.1 σQ → R.1 ((σQ ⋆ σ).get s))
    (σ : Resource)
    (hex : ∃ σ₁ σ₂, ∃ (s : (σ₁ ⋆ σ₂).isSome = true),
      (σ₁ ⋆ σ₂).get s ≤ σ ∧ P.1 σ₁ ∧ Q.1 σ₂) :
    R.1 σ := by
  obtain ⟨σ₁, σ₂, s, h_le, hP, hQ⟩ := hex
  have hr := h σ₁ hP σ₂ (Pcm.comm σ₂ σ₁ ▸ s) hQ
  simp only [Pcm.comm σ₂ σ₁] at hr
  exact R.2 _ σ h_le hr

private lemma persistently_and_l_lem {P Q : IProp Resource}
    (σ : Resource) (h : P.1 1 ∧ Q.1 σ) :
    ∃ σ₁ σ₂, ∃ (σ₁₂ : (σ₁ ⋆ σ₂).isSome = true),
      ↓σ₁₂ ≤ σ ∧ P.1 σ₁ ∧ Q.1 σ₂ := by
  refine ⟨1, σ, ?_, ?_, h.1, h.2⟩
  · rw [Pcm.one_mul]; rfl
  · simp [Pcm.one_mul]



/-! ### BI instance -/

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

  and_elim_l := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ ⟨h, _⟩; exact h
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ ⟨_, h⟩; exact h
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR σ h_P
    exact ⟨h_PQ σ h_P, h_PR σ h_P⟩

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h; exact Or.inl h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h; exact Or.inr h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR σ h_PQ
    exact h_PQ.elim (h_PR σ) (h_QR σ)

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro P _ _ h_PQR σ h_P σ' σ_le_σ' h_Q
    exact h_PQR σ' ⟨P.2 σ σ' σ_le_σ' h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    exact h_PQR σ h_P σ (Preorder.le_refl σ) h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ σ h_P p hp
    exact h_PΨ p hp σ h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ _ hp _ h_Ψ
    exact h_Ψ _ hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ _ hp _ h_Ψ
    exact ⟨_, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp σ h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ h_PQ h_P'Q' σ ⟨σ₁, σ₂, h_s, h_le, hP, hP'⟩
    exact ⟨σ₁, σ₂, h_s, h_le, h_PQ σ₁ hP, h_P'Q' σ₂ hP'⟩

  emp_sep := by
    simp only [BI.sep, BI.emp]
    exact ⟨emp_sep_mp, emp_sep_mpr⟩

  sep_symm := by
    simp only [BI.Entails, BI.sep]
    exact sep_symm_lem

  sep_assoc_l := by
    simp only [BI.Entails, BI.sep]
    exact sep_assoc_lem

  wand_intro := by
    simp only [BI.Entails, BI.sep, BI.wand]
    exact wand_intro_lem

  wand_elim := by
    simp only [BI.Entails, BI.sep, BI.wand]
    exact wand_elim_lem

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ _ h_P
    exact h_PQ 1 h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h; exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro σ P; trivial
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ h; exact h
  persistently_sExists_1 := by
    simp only [BI.Entails, BI.persistently, BI.exists]
    intro _ σ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ σ ⟨_, _, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
    exact persistently_and_l_lem

  later_mono := id
  later_intro _ := id
  later_sForall_2 := by
    simp only [BI.Entails, BI.pure, BI.imp, BI.later, BI.sForall]
    intro Φ σ h p hp
    have := h ⟨fun σ ↦ ∀ σ', σ ≤ σ' → Φ p → p.1 σ',
      fun σ₁ σ₂ h₁₂ h₁ σ' h₂ ↦ h₁ σ' (h₁₂.trans h₂)⟩ ⟨_, rfl⟩
    exact this σ (Preorder.le_refl σ) hp
  later_sExists_false := by
    simp only [BI.Entails, BI.later, BI.or, BI.exists, BI.pure]
    intro _ _ ⟨p, hp⟩
    exact Or.inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ => id, fun _ => id⟩
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em := by
    simp only [BI.Entails, BI.later, BI.or, BI.imp, BI.pure]
    intro _ σ _
    exact Or.inr (fun _ _ hf ↦ hf.elim)

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
