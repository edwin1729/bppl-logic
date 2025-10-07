import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Category.MeasCat

-- unused?
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open ProbabilityTheory Kernel

abbrev var := String

--/-- Terms in BPPL -/
--inductive te where
--  | ins: Nat → te → te -- (i,t)
--  | case: te → (Nat → var → te) → te
--  | unit : te
--  | prod: te → te → te
--  | proj: te → Nat → te
--  -- | f(t)
--  | var: var → te
--  | ret: te → te -- return(t)
--  | lt: var → te → te -- let x = t in u
--  | sample: te → te
--  | score: te → te
--  | normalize: te → te
--
--mutual
--  inductive t where
--    | typed: t' → 𝔸 → t
--
--  inductive t' where
--    | ins: Nat → t → t' -- (i,t)
--    | case: t → (Nat → var → t) → t'
--    | unit : t'
--    | prod: t → t → t'
--    | proj: t → Nat → t'
--    -- | f(t)
--    | var: var → t'
--    | ret: t → t' -- return(t)
--    | lt: var → t → t' -- let x = t in u
--    | sample: t → t'
--    | score: t → t'
--    | normalize: t → t'
--end

inductive 𝔸 where
  | R
  | P: 𝔸 → 𝔸 -- Giry monad
  | unit -- unit
  | prod: 𝔸 → 𝔸 → 𝔸
  | sum: 𝔸 → 𝔸 → 𝔸
  -- | sum (ι : Type*) [Countable ι] : (ι → 𝔸) → 𝔸 -- ⨆ 𝔸ᵢ

/-- Typed terms of a Baysian probabilistic programming language.
The types are only required at binding sites: `let` and `case` -/
inductive t where
  | ins: Nat → t → t -- (i,t)
  | case: t → (Nat → var × 𝔸 → t) → t
  | unit : t
  | prod: t → t → t
  | proj: t → Nat → t
  | var: var → t
  | ret: t → t -- return(t)
  | lt: var × 𝔸 → t → t -- let x = t in u
  | sample: t → t
  | score: t → t
  | normalize: t → t

-- def measure_iunion (ι : Type*) (f: ι → Σ T: Type, MeasurableSpace T) :
--   MeasurableSpace T₁ ⊕ T₂ := sorry

-- marked as noncomputable because of Giry
noncomputable def type_denote (ty: 𝔸): Σ (T: Type), MeasurableSpace T :=
  match ty with
  | 𝔸.R => ⟨ℝ, borel ℝ⟩
  | 𝔸.P ty' =>
    let ⟨ty, _⟩ := type_denote ty'
    let foo := MeasCat.Giry.obj (MeasCat.of ty)
    ⟨foo, foo.str⟩
  | 𝔸.unit => ⟨PUnit, PUnit.instMeasurableSpace⟩ -- unit
  | 𝔸.prod ty₁' ty₂' =>
    let ⟨ty₁, _⟩ := type_denote ty₁'
    let ⟨ty₂, _⟩ := type_denote ty₂'
    ⟨ty₁ × ty₂, (inferInstance : MeasurableSpace (ty₁ × ty₂))⟩
  | 𝔸.sum ty₁' ty₂' =>
    let ⟨ty₁, _⟩ := type_denote ty₁'
    let ⟨ty₂, _⟩ := type_denote ty₂'
    ⟨ty₁ ⊕ ty₂, (inferInstance : MeasurableSpace (ty₁ ⊕ ty₂))⟩

-- abbrev denotation: -- (var → 𝔸) → ()

def type_prod (tys: List Type): Type :=
  match tys with
  | [] => Unit
  | [ty] => ty
  | ty::tys => ty × type_prod tys

inductive out (α : MeasCat) where
  | det: Σ (β : MeasCat) (f: α → β), Measurable f

def denote (vs: List (var × t × 𝔸)) (te: t) : Except String ()
