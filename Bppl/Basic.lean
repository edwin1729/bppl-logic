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

inductive 𝔸 where
  | R
  | P: 𝔸 → 𝔸 -- Giry monad
  | unit -- unit
  | prod: 𝔸 → 𝔸 → 𝔸
  | sum: 𝔸 → 𝔸 → 𝔸
  -- | sum (ι : Type*) [Countable ι] : (ι → 𝔸) → 𝔸 -- ⨆ 𝔸ᵢ

mutual
  structure t where
    unty_te : t'
    ty: 𝔸

  -- could use higher order syntax. Which is perhaps cleaner atleast for the case arm.
  -- But need to modufy how the context works a bit so for now just putting it on the programmer
  inductive t' where
    | inl: t → t' -- (i,t)
    | inr: t → t' -- (i,t)
    -- the 2nd and 3rd `t` is uses the `var` as a free variable
    | case: t → var → t → t → t'
    | unit : t'
    | prod: t → t → t'
    | proj: t → Nat → t'
    -- | f(t)
    | var: var → t'
    | ret: t → t' -- return(t)
    | lt: var → t → t' -- let x = t in u
    | sample: t → t'
    | score: t → t'
    | normalize: t → t'
end

/-- Typed terms of a Baysian probabilistic programming language.
The types are only required at binding sites: `let` and `case` -/
--inductive t where
--  | ins: Nat → t → t -- (i,t)
--  | case: t → (Nat → var × 𝔸 → t) → t
--  | unit : t
--  | prod: t → t → t
--  | proj: t → Nat → t
--  | var: var → t
--  | ret: t → t -- return(t)
--  | lt: var × 𝔸 → t → t -- let x = t in u
--  | sample: t → t
--  | score: t → t
--  | normalize: t → t

-- def measure_iunion (ι : Type*) (f: ι → Σ T: Type, MeasurableSpace T) :
--   MeasurableSpace T₁ ⊕ T₂ := sorry

-- marked as noncomputable because of Giry
noncomputable def type_denote' (ty : 𝔸) : Σ (T: Type), MeasurableSpace T :=
  match ty with
  | 𝔸.R => ⟨ℝ, borel ℝ⟩
  | 𝔸.P ty' =>
    let ⟨ty, _⟩ := type_denote' ty'
    let foo := MeasCat.Giry.obj (MeasCat.of ty)
    ⟨foo, foo.str⟩
  | 𝔸.unit => ⟨PUnit, PUnit.instMeasurableSpace⟩ -- unit
  | 𝔸.prod ty₁' ty₂' =>
    let ⟨ty₁, _⟩ := type_denote' ty₁'
    let ⟨ty₂, _⟩ := type_denote' ty₂'
    ⟨ty₁ × ty₂, (inferInstance : MeasurableSpace (ty₁ × ty₂))⟩
  | 𝔸.sum ty₁' ty₂' =>
    let ⟨ty₁, _⟩ := type_denote' ty₁'
    let ⟨ty₂, _⟩ := type_denote' ty₂'
    ⟨ty₁ ⊕ ty₂, (inferInstance : MeasurableSpace (ty₁ ⊕ ty₂))⟩

noncomputable def type_denote (ty' : 𝔸) : MeasCat :=
  let ⟨ty, _⟩ := type_denote' ty'
  MeasCat.of ty

-- abbrev denotation: -- (var → 𝔸) → ()

def type_prod (tys : List MeasCat): MeasCat :=
  match tys with
  | [] => MeasCat.of PUnit
  | [ty] => ty
  | ty::tys => MeasCat.of (ty × type_prod tys)

abbrev denotation_ty (α β : MeasCat) :=
  {f : α → β // Measurable f} ⊕ Kernel α β

-- get deterministic denotation or fail
def get_det {α β : MeasCat} (den : denotation_ty α β) (err_msg : String)
  : Except String {f : α → β // Measurable f} :=
  den.elim (fun det ↦ Except.ok det) (fun _ ↦ Except.error err_msg)

-- get probabilistic denotation or fail
def get_prob {α β : MeasCat} (den : denotation_ty α β) (err_msg : String)
  : Except String (Kernel α β) :=
  den.elim (fun _ ↦ Except.error err_msg) (fun prob ↦ Except.ok prob)

-- I don't aim to type check here. I do a sort of optimistic type checking.
-- (Probably called dynamic type checking actually)
-- Invalidly typed terms recieve undefined semantics instead of failing as expected
-- A type checker is best added as a separate step later
def denote (vs: List (var × t × 𝔸)) (te : t) : Except String
  (denotation_ty (type_prod ((List.map (fun (a,b,c) ↦ (type_denote c)) vs))) (type_denote te.ty)) :=
  match te.unty_te with
  | everyhting => sorry
  --| t'.inl te => do
  --  let te_denotation ← (denote vs te)
  --  let measurable_fn ← get_det te_denotation "Only deterministic values allowed in an injection"
  --  pure (Sum.inl ((fun x ↦ Sum.inl x) ∘ measurable_fn))
  --  -- pure ((fun x ↦ (0, x)) ∘ measurable_fn)
  --  -- pure (false, te'') -- arbitrary choice to represent left with false
  --| t'.inl te => do
  --  let te' := get_det (denote vs te) "Only deterministic values allowed in an injection"
  --  return (true, te') -- arbitrary choice to represent right with true
  -- This arm is interesting if typechecking and not using the binary sum type and
  -- using the countably infinite sum type from the paper
  --| t'.case te name left right => do
  --  if
  --  let foo := denote vs te
  --| t'.unit => t'
  --| t'.prod: t → t → t'
  --| t'.proj: t → Nat → t'
  ----t'. | f(t)
  --| t'.var: var → t'
  --| t'.ret: t → t' -- return(t)
  --| t'.lt: var → t → t' -- let x = t in u
  --| t'.sample: t → t'
  --| t'.score: t → t'
  --| t'.normalize: t → t'


-- files to look into for the disintegration theorem
-- Basic, density, standard borel, unique
