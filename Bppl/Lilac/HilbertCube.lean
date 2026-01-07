
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.Topology.UnitInterval

-- set_option trace.Meta.synthInstance true

open Mathlib.Tactic.Borelize MeasurableSpace
-- The Kripke Resource Monoid is at the core of Lilac

#check (inferInstance : TopologicalSpace unitInterval)
#check (inferInstance : MeasurableSpace unitInterval)


-- better to define this constructively? As an inductive definition
def countable_prod {α : Type*} (f : ℕ → Set α) : Set (Set α) :=
  { s | ∀ i : ℕ, ∃ a : α, a ∈ f i ∧ a ∈ s }


notation "Measurable[" mα ", " mβ "]" => @Measurable _ _ mα mβ

-- [0, 1]ᴺ
def HilbertCube := ℕ → unitInterval

-- We define the standard borel σ-algebra for the Hilbert cube.
-- Note that each element of the Hilbert cube is itself a countable set


instance : MeasurableSpace HilbertCube where
  MeasurableSet' s := sorry --Set α → Prop
  measurableSet_empty := sorry -- MeasurableSet' ∅
  measurableSet_compl := sorry -- ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  measurableSet_iUnion := sorry -- ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)
