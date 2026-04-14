/-
Copyright (c) 2026 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/


import Mathlib
import Mathlib.Probability.ProbabilityMassFunction.Constructions
/-! Playing with Parametric Abstract Higher Order Syntax (PHOAS),
and evaluating it's suitability. The glaring concern is that PHOAS may not be
able to provide a notion of the map from the environment to a term being measurable.
To elaborate, perhaps it's straightforward to show that the map from a signle variable to
a term's denotation is measurable. But to express that a map from a List of variables (enviornment)
to a term is measurable doesn't seem possible.

reference: https://lean-lang.org/examples/1900-1-1-parametric-higherorder-abstract-syntax/
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
universe u v
-- Primitives

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

/-- Since we don't want to use our custom HList wiht the requirement of MeasurableSpace on our types
TProd provides a MeasurableSpace instance -/
def List.TProd.get : List.TProd β is → Member i is → β i
  | v, .head => v.1
  | v, .tail h => List.TProd.get v.2 h

theorem List.TProd.measurable_get [∀ i, MeasurableSpace (β i)] (mem : Member i is) :
    Measurable fun v : List.TProd β is => v.get mem := by
  induction mem with
  | head => exact measurable_fst
  | tail _ ih => exact ih.comp measurable_snd

abbrev MeasurableFun (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  := {f: α → β // Measurable f}

notation α " -m→ " β => MeasurableFun α β

instance instCoeMeasurableFun [MeasurableSpace α] [MeasurableSpace β] :
    CoeFun (α -m→ β) (fun _ => α → β) where
  coe f := f.val


inductive Ty where
  | bool
  | G : Ty → Ty
  | real : Ty
  | prod : Ty → Ty → Ty

inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : rep ty → Term' rep ty
  | ret : Term' rep ty → Term' rep (.G ty)
  | bind : Term' rep (.G ty₁) → (rep dom → Term' rep (.G ty₂)) → Term' rep (.G ty₂)
  | unif01 : Term' rep (.G .real)
  | pair : Term' rep ty₁ → Term' rep ty₂ → Term' rep (.prod ty₁ ty₂)

def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty

open Term' (unif01)
def unif2 : Term (Ty.prod .real .real).G :=
  unif01.bind ( fun X ↦
  unif01.bind ( fun Y ↦
  .ret (.pair (.var X) (.var Y))
))

def countVars : Term' (fun _ => Unit) ty → Nat
  | .var _    => 1
  | .ret a => countVars a
  | .bind a b  => countVars a + countVars (b ())
  | .unif01 => 0
  | .pair a b => countVars a + countVars b

example : countVars unif2 = 2 :=
  rfl

noncomputable section
-- Most of the MeasurableSpace instance provided in
-- Mathlib.MeasureTheory.MeasurableSpace.Instances
@[reducible] def Ty.den : Ty → MeasCat
  | bool => .of Bool
  | G ty => MeasCat.Measure.obj (ty.den) --: Ty → Ty
  | real => .of ℝ
  | prod ty₁ ty₂ => .of (ty₁.den × ty₂.den)
