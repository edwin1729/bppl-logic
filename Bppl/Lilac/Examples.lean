/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Appl
import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules.WP

import Iris.ProofMode

/-! # Examples of proofs using the Iris proof mode instantiated to Lilac

- `unif1`: which samples from `unif01` in the language and shows the
corresponding result in the logic.
- `unif2`: like `unif1` but takes 2 independent samples `X` an `Y` and demonstrates
construction of a separating conjunct
- `half`: Given a random variable `X` in context and a uniform sample in [0,1], `Y`
  shows 𝔼[XY] = 𝔼[X]/2

-/

open Appl
abbrev mul (a b : RV ⟪Ty.real⟫) : RV ⟪Ty.real⟫ := ⟨⟨λ ω ↦ a ω * b ω, sorry⟩, sorry⟩

open LProp Appl Appl.Term Member Iris.BI ProbabilityTheory MeasurableFun WP
/-! There is still the unsolved problem of the programs being expressed via de brujin indices.
Maybe we can just have string based mapping somehow. -/
noncomputable section
-- Maybe use parametric abstract higher order syntax instead to make

abbrev nil : RV (List.TProd (⟪·⟫) []) := ⟨⟨λ _ ↦ PUnit.unit, measurable_const⟩, sorry⟩

namespace Unif1
abbrev unif1 : Term [] Ty.real.G :=
  unif01.bind (
  ret (var head)
)

abbrev post1 : LProp := wp (unif1.den ∘ᵣ nil) (λ (X : RV ℝ) ↦ @LProp.dist Ty.real X lebI')

lemma hrw {A : Ty} {X : RV ⟪A⟫} : ((var head).den ∘ᵣ (X ;; nil)) = X := by rfl

theorem unif1_spec : iprop(⊢ post1) := by
  iapply wp_bind
  iapply wp_unif
  iintro %X
  iintro H
  iapply wp_ret
  rw [hrw]
  iexact H

end Unif1

namespace Unif2

abbrev unif2 : Term [] (Ty.prod .real .real).G :=
  unif01.bind (
  unif01.bind (
  ret (pair (var (tail head)) (var head))
))

notation:10 D ".ₘ1" => (measurableFun_fst ∘ᵣ D)
notation:10 D ".ₘ2" => (measurableFun_snd ∘ᵣ D)

abbrev post2 : LProp := wp (unif2.den ∘ᵣ nil) (λ (Z : RV ⟪Ty.prod .real .real⟫) ↦
  iprop((Z.ₘ1) ∼ lebI' ∗ (Z.ₘ2) ∼ lebI'))

lemma hrw2₁ {A : Ty} (X Y : RV ⟪A⟫) : (measurableFun_fst ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = X := by rfl
lemma hrw2₂ {A : Ty} (X Y : RV ⟪A⟫) : (measurableFun_snd ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = Y := by rfl

theorem unif2_spec : iprop(⊢ post2) := by
  rw [post2]
  iintro
  iapply wp_bind
  iapply wp_unif
  iintro %X HX
  iapply wp_bind
  iapply wp_unif
  iintro %Y HY
  iapply wp_ret
  rw [hrw2₁, hrw2₂]
  isplitl [HX]
  · iexact HX
  · iexact HY

end Unif2

namespace Half

abbrev half : Term [Ty.real] Ty.real.G :=
  unif01.bind (
    ret (.arith .mul (var (tail head)) (var head))
  )

-- abbrev X : RV ⟪Ty.real⟫ := ⟨⟨λ ω ↦ ω 0, sorry⟩, sorry⟩

abbrev envX : RV (List.TProd (⟪·⟫) [Ty.real]) := ⟨⟨λ ω ↦ (ω 0, PUnit.unit), sorry⟩, sorry⟩

abbrev post_half (X : RV ⟪Ty.real⟫) : LProp := wp (half.den ∘ᵣ (X ;; nil)) (λ (Z : RV ℝ) ↦
    iprop(∃ e, 𝔼[Z]=e/2 ∧ 𝔼[X]=e))

lemma hrw (X Y : RV ⟪Ty.real⟫) : ((arith Arith.mul (var head.tail) (var head)).den ∘ᵣ Y ;; X ;; nil) = mul X Y := by rfl

theorem half_spec (X : RV ⟪Ty.real⟫) : own X ⊢ post_half X := by
  iintro hX
  rw [post_half]
  iapply wp_bind
  iapply wp_unif
  iintro %Y HY
  iapply wp_ret
  rw [hrw]
  sorry

end Half
