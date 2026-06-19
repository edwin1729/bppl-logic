/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/

import Bppl.Lilac.Appl
import Bppl.Lilac.Assertion
import Bppl.Lilac.ProofRules.WP
import Bppl.Lilac.ProofRules.Expectation

import Iris.ProofMode

/-! # Examples of proofs using the Iris proof mode instantiated to Lilac

- `unif1`: which samples from `unif01` in the language and shows the
corresponding result in the logic.
- `unif2`: like `unif1` but takes 2 independent samples `X` an `Y` and demonstrates
construction of a separating conjunct
- `half`: Given a random variable `X` in context and a uniform sample in [0,1], `Y`
  shows 𝔼[XY] = 𝔼[X]/2

-/

open LProp Appl Appl.Term Member Iris.BI ProbabilityTheory MeasurableFun WP RV
/-! There is still the unsolved problem of the programs being expressed via de brujin indices.
Maybe we can just have string based mapping somehow. -/
noncomputable section
-- Maybe use parametric abstract higher order syntax instead to make

abbrev nil : RV (List.TProd (⟪·⟫) []) :=
  ⟨⟨λ _ ↦ PUnit.unit, measurable_const⟩, RV.ff_const PUnit.unit⟩

notation "#0" => var head
notation "#1" => var (tail head)

namespace Unif1
-- abbrev post1 : LProp := wp (unif1.den ∘ᵣ nil) (λ X : RV ⟪Ty.real⟫ ↦ iprop(X ∼ unif01_sem))

abbrev unif1 : Term [] Ty.real.G :=
  unif01.bind (
  ret (#0)
)

lemma hrw {A : Ty} {X : RV ⟪A⟫} : ((#0).den ∘ᵣ (X ;; nil)) = X := by rfl

theorem unif1_spec :
    iprop(⊢ wp (unif1.den ∘ᵣ nil) (λ X : RV ⟪Ty.real⟫ ↦ iprop(X ∼ unif01_sem))) := by
  iapply wp_bind
  iapply wp_unif
  iintro %X HX
  iapply wp_ret
  rw [hrw]
  iexact HX

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
  iprop((Z.ₘ1) ∼ unif01_sem ∗ (Z.ₘ2) ∼ unif01_sem))

lemma hrw2₁ {A : Ty} (X Y : RV ⟪A⟫) :
  (measurableFun_fst ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = X := by rfl
lemma hrw2₂ {A : Ty} (X Y : RV ⟪A⟫) :
  (measurableFun_snd ∘ᵣ ((var head.tail).pair (var head)).den ∘ᵣ (Y ;; X ;; nil)) = Y := by rfl

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
    ret (#1 * #0)
  )

lemma hrw (X Y : RV ⟪Ty.real⟫) : ((arith Arith.mul #1 #0).den ∘ᵣ Y ;; X ;; nil) = X * Y := by rfl
lemma hr2 (X Y : RV ⟪Ty.real⟫) : ((arith Arith.mul #1 #0).den ∘ᵣ Y ;; X ;; nil)
  = ((Term.den ((#1 * #0): Term [Ty.real, Ty.real] Ty.real)) ∘ᵣ Y ;; X ;; nil) := by rfl

theorem half_spec (X : RV ⟪Ty.real⟫) :
    own X ⊢ wp (half.den ∘ᵣ (X ;; nil))
               (λ XY : RV ℝ ↦ iprop(∃ e, 𝔼[XY]=e/2 ∧ 𝔼[X]=e)) := by
  iintro hX
  iapply wp_bind
  iapply wp_unif
  iintro %Y hY
  iapply wp_ret
  rw [← hr2, hrw]
  ihave hX := expectation_of_own $$ hX
  icases hX with ⟨%e, he⟩
  iexists e
  isplit
  · iexpect_prod he hY
    iexists e, 0.5
    ihave expY := expectation_of_unif01 $$ hY
    isplit
    · iexact he
    · isplit
      · iexact expY
      · ipure_intro
        ring
  · iexact he
  -- iexists (∫ ω, X ω ∂(Ω.μ))

end Half
