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
  and P Q        := ⟨fun s σ ↦ P.1 s σ ∧ Q.1 s σ, /-fun _ _ _ _ hσ₁ ↦ sorry⟩-/ by
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

end Iris.Instances.Intuitionistic
