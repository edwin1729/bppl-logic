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

open LProp Appl Appl.Term Member Iris.BI ProbabilityTheory MeasurableFun WP TypeClasses

/-! The examples in this file need a a lot of revision (and metaprogramming) to
make an ergonomic experience -/

-- Maybe use parametric abstract higher order syntax instead to make
abbrev unif2 : Term [] (Ty.prod .real .real).G :=
  unif01.bind (
  unif01.bind (
  ret (pair (var (tail head)) (var head))
))

def unif1 : Term [] Ty.real.G :=
  unif01.bind (
  ret (var head)
)

-- TODO `⟪Ty.real⟫` shoud reduce to `ℝ` providing this instance directly
instance : Preorder ⟪Ty.real⟫ := sorry

-- TODO 1) the deterministic context never get's used hence it isn't
-- inferred that we want to use `Ty` for both `TyDet` and `TyRand`. Can just hardcode that buttt...
-- This is indicative of a problem with deterministic environments.
-- When do we ever use them? Can it be removed?
lemma unif1_prop
    : ⊢ (@wp Ty _ _ _ _ _ _ (fun _ ↦ unif1.den) iprop((fun _d_env ↦ ⟨fun r_env ↦ r_env.get head , List.TProd.measurable_get head⟩) ∼ (fun _ ↦ uniformOn (Set.Icc (0 : ℝ) (1: ℝ)))) : LProp [] []) := sorry

abbrev post : @LProp Ty Ty _ _ [] [] :=
  wp ⦃unif2⦄ (LProp.dist (fun _ ↦ measurableFun_fst ∘ₘ measurableFun_fst) WP.unif01_sem)

theorem unif2_spec : iprop(⊢ post) := by
  rw [post]
  iintro
  iapply wp_bind
  iapply wp_unif
  iintro %x

  dsimp [substRandVar]

  sorry
