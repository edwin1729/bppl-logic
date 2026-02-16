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
by a more informative resource. -/
abbrev IProp (Env Resource : Type*) [Krm Resource]
  := {sem : Env → Resource → Prop // ∀ s σ₁ σ₂, σ₁ ≤ σ₂ → sem s σ₁ → sem s σ₂}

instance instBIBase : BIBase (IProp Env Resource) where
  Entails P Q    := ∀ s σ, P.1 s σ → Q.1 s σ
  emp            := ⟨fun _ _ ↦ True, fun _ _ _ _ _ ↦ trivial⟩
  pure φ         := ⟨fun _ _ ↦ φ, fun _ _ _ _ hσ₁ ↦ hσ₁⟩
  and P Q        := ⟨fun s σ ↦ P.1 s σ ∧ Q.1 s σ, by
    intro s σ₁ σ₂ hle ⟨hPσ₁, hQσ₁⟩
    exact ⟨P.2 s σ₁ σ₂ hle hPσ₁ , Q.2 s σ₁ σ₂ hle hQσ₁⟩
  ⟩
  or P Q        := ⟨fun s σ ↦ P.1 s σ ∨ Q.1 s σ,
    fun s σ1 σ2 hle hσ1 => hσ1.elim (Or.inl ∘ P.2 s σ1 σ2 hle) (Or.inr ∘ Q.2 s σ1 σ2 hle)
  ⟩
  imp P Q        := ⟨fun s σ ↦ ∀ σ', σ ≤ σ' → (P.1 s σ' → Q.1 s σ'),
    fun s σ₁ σ₂ σ₁_le_σ₂ hσ₁ σ' σ₂_le_σ' hPσ' ↦ hσ₁ σ' (σ₁_le_σ₂.trans σ₂_le_σ') hPσ'
  ⟩
  sForall Ψ      := ⟨fun s σ ↦ ∀ p, Ψ p → p.1 s σ, by
    intro s σ₁ σ₂ σ₁_le_σ₂ hσ₁ p hp
    exact p.2 s σ₁ σ₂ σ₁_le_σ₂ (hσ₁ p hp)
  ⟩
  sExists Ψ      := ⟨fun s σ ↦ ∃ p, Ψ p ∧ p.1 s σ, by
    intro s σ₁ σ₂ σ₁_le_σ₂ ⟨p, hp, hpσ₁⟩
    exact ⟨p, hp, p.2 s σ₁ σ₂ σ₁_le_σ₂ hpσ₁⟩
  ⟩
  sep P Q        := ⟨fun s σ ↦ ∃ σ₁ σ₂, σ₁ ⋆ σ₂ ≤ σ ∧ P.1 s σ₁ ∧ Q.1 s σ₂, by
    intro s σ₁ σ₂ σ₁_le_σ₂ ⟨σP, σQ, hσPQ, hP, hQ⟩
    use σP, σQ
    constructor
    · sorry
      -- have foo : some σ₁ ≤ some σ₂ := by exact σ₁_le_σ₂
      -- #check Preorder.le_transWithBot.instPreorder
      -- #check WithBot.
      -- exact @Preorder.le_trans (Option Resource) WithBot.preorder _ (some σ₁) (some σ₂) hσPQ foo
      -- trans (some σ₂)

    · sorry
    --   · σ₁_le_σ₂
    --   · hσPQ
    --  by trans
    --  --hσPQ.trans σ₁_le_σ₂
    --  · sorry
    --  · sorry
    --  , hP, hQ⟩
  ⟩
  wand P Q       := ⟨fun s σ ↦ ∀ σp, ∃ σq, σp ⋆ σ = some σq ∧ (P.1 s σp → Q.1 s σq), sorry⟩
  persistently P := ⟨fun s σ ↦ P.1 s 1, sorry⟩
  later P        := ⟨fun s σ ↦ P.1 s σ, sorry⟩

instance : Std.Preorder (Entails (PROP := IProp Env Resource)) where
  refl := by
    simp only [BI.Entails]
    intro _ _ _ h
    exact h
  trans := by
    simp only [BI.Entails]
    intro _ _ _ h_xy h_yz s σ h_x
    apply h_yz s σ
    apply h_xy s σ
    exact h_x

instance : COFE (IProp Env Resource) :=
  COFE.ofDiscrete Eq equivalence_eq

/-- These proofs have been ported from the Iris-lean to the classical separation logic,
modified as necessary. The similarities between the two logics is the lack of step-indexing
and general similarity in non-spatial axioms -/
instance instBI : BI (IProp Env Resource) where
  entails_preorder := by infer_instance
  equiv_iff {P Q} := ⟨
    fun h : P = Q => h ▸ ⟨fun _ _ φ ↦ φ, fun _ _ φ ↦ φ⟩,
    fun ⟨h₁, h₂⟩ => by ext s σ; exact ⟨h₁ s σ, h₂ s σ⟩
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

  pure_intro h _ _ _ := h
  pure_elim' h_φP s σ h_φ := h_φP h_φ s σ ⟨⟩

  and_elim_l := by
    intros
    simp only [BI.Entails, BI.and]
    intro _ _ h
    exact h.left
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ _ h
    exact h.right
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR s σ h_P
    constructor
    · exact h_PQ s σ h_P
    · exact h_PR s σ h_P

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR s σ h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR s σ h_P
    case inr h_Q =>
      exact h_QR s σ h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR s σ h_P Ω' Ω_le_Ω' h_Q
    sorry -- TODO ≤ (actually the below case is the problem)
    -- exact h_PQR s σ ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR s σ ⟨h_P, h_Q⟩
    sorry -- TODO ≤
    -- exact h_PQR s σ h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ s σ h_P p hp
    exact h_PΨ p hp s σ h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp _ _ h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp _ _ h_Ψ
    exact ⟨p, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ s σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp s σ h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ h_PQ h_P'Q' s σ ⟨σ₁, σ₂, h_Ω, h_P, h_P'⟩
    use σ₁, σ₂
    exact ⟨h_Ω, h_PQ s σ₁ h_P, h_P'Q' s σ₂ h_P'⟩
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp]

    intro _ _ ⟨σ₁, σ₂, h_Ω, h_emp, h_P⟩
    -- Ω
    -- rw [h_emp] at h_union
    -- rw [h_emp, Pcm.one_mul, Option.some_le_some] at h_Ω
    sorry -- TODO ≤
    -- rw [← h_Ω]
    -- exact h_Ω ▸ h_P
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp]
    sorry -- TODO ≤ (This is actually provable. Just inverse of the above broken case
    -- so skipped)
  sep_symm := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ ⟨σ₁, σ₂, h_union, h_P, h_Q⟩
    use σ₂, σ₁
    rw [Pcm.comm]
    exact ⟨h_union, h_Q, h_P⟩
  sep_assoc_l := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ _
      ⟨Ω₁₂, Ω₃, h_Ω₁₂₃ₗ, ⟨Ω₁, Ω₂, h_Ω₁₂, h_P₁, h_P₂⟩, h_P₃⟩
    use Ω₁
    -- usage of Pcm.assoc is obstructed by ≤
    sorry  -- Todo ≤

  -- suspect these might change due to ≤
  wand_intro := sorry
  wand_elim := sorry

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ s _ h_P
    exact h_PQ s 1 h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro s σ P
    trivial
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ _ h
    exact h
  persistently_sExists_1 := by
    simp only [BI.Entails, BI.persistently, BI.exists]
    intro _ _ _ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ _ _ ⟨_, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
    intro _ _ _ σ ⟨h_P, h_Q⟩
    apply Exists.intro 1
    apply Exists.intro σ
    constructor
    · rw [Pcm.one_mul, Option.some_le_some]
    constructor
    · exact h_P
    · exact h_Q

  later_mono := id
  later_intro _ _ := id
  later_sForall_2 {Φ} s σ P := by
    simp only [later, sForall] -- for clarity, can delete
    intro Q h_Q
    let foo := P Q
    apply foo
    use Q
    simp [BI.pure, later]
    ext s σ
    constructor
    ·
      intro P'
      exact P' σ (le_refl _) h_Q
    ·
      intro q Ω' h_Ω' P'
      sorry -- TODO ≤ (require that bigger )

  later_sExists_false _ _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ _ => id, fun _ _ => id⟩
  later_persistently := ⟨fun _ _ => id, fun  _ _ => id⟩
  later_false_em _ _ h := .inr fun _ _ => (by
    simp [later] at h
    sorry -- TODO ≤ :(
    -- exact h
  )


end Iris.Instances.Intuitionistic
