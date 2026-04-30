/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Appl
import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules

import Iris.ProofMode

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.style.lambdaSyntax false

open LProp Appl Appl.Term Member Iris.BI ProbabilityTheory MeasurableFun WP Substitution

/-! There is still the unsolved problem of the programs being expressed via de brujin indices.
Maybe we can just have string based mapping somehow. -/

-- Maybe use parametric abstract higher order syntax instead to make
abbrev unif1 : Term [] Ty.real.G :=
  unif01.bind (
  ret (var head)
)

abbrev unif2 : Term [] (Ty.prod .real .real).G :=
  unif01.bind (
  unif01.bind (
  ret (pair (var (tail head)) (var head))
))


abbrev nil : RV (List.TProd (⟪·⟫) []) := ⟨λ _ ↦ PUnit.unit, measurable_const⟩

abbrev post1 : LProp := wp (unif1.den ∘ₚ nil) (λ (X : RV ℝ) ↦ @LProp.dist Ty.real X WP.unif01_sem)

lemma hrw {A : Ty} {X : RV ⟪A⟫} : ((var head).den ∘ₚ (X ; nil)) = X := by rfl

theorem unif1_spec : iprop(⊢ post1) := by
  iapply wp_bind
  iapply wp_unif
  iintro %X
  iintro H
  iapply wp_ret
  rw [hrw]
  iexact H

notation:10 D ".ₘ1" => (measurableFun_fst ∘ₚ D)
notation:10 D ".ₘ2" => (measurableFun_snd ∘ₚ D)

abbrev post2 : LProp := wp (unif2.den ∘ₚ nil) (λ (Z : RV ⟪Ty.prod .real .real⟫) ↦
  iprop((Z.ₘ1) ∼ WP.unif01_sem ∗ (Z.ₘ2) ∼ WP.unif01_sem))

lemma hrw2₁ {A : Ty} (X Y : RV ⟪A⟫) : (measurableFun_fst ∘ₚ ((var head.tail).pair (var head)).den ∘ₚ (Y ; X ; nil)) = X := by rfl
lemma hrw2₂ {A : Ty} (X Y : RV ⟪A⟫) : (measurableFun_snd ∘ₚ ((var head.tail).pair (var head)).den ∘ₚ (Y ; X ; nil)) = Y := by rfl

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
