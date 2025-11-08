import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Category.MeasCat

-- unused?
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open ProbabilityTheory Kernel

abbrev var := String

/-- Types in BPPL -/
inductive 𝔸 where
  | R
  | P: 𝔸 → 𝔸 -- Giry monad
  | unit -- unit
  | prod: 𝔸 → 𝔸 → 𝔸
  | sum: 𝔸 → 𝔸 → 𝔸
  -- | sum (ι : Type*) [Countable ι] : (ι → 𝔸) → 𝔸 -- ⨆ 𝔸ᵢ
  deriving BEq

/-- Terms in BPPL -/
inductive te where
  | inl: te → te -- (i,t)
  | inr: te → te -- (i,t)
  | case: te → var → te → te → te
  | unit : te
  | prod: te → te → te
  | πₗ : te → te
  | πᵣ : te → te
  -- | f(t)
  | var: var → 𝔸 → te
  | ret: te → te -- return(t)
  | lt: var → te → te -- let x = t in u
  | sample: te → te
  | score: te → te
  | normalize: te → te

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
    | πₗ : t → t'
    | πᵣ : t → t'
    -- | f(t)
    | var: var → t'
    | ret: t → t' -- return(t)
    | lt: var → t → t' -- let x = t in u
    | sample: t → t'
    | score: t → t'
    | normalize: t → t'
end

-- constrain terms to only be well-typed if there aren't pointless `inl` and `inr` injections
-- Essentially we demand the terms' structure is such that type checking local, as opposed to
-- the usual non-local strategies with type variables
def infer_type (term : te) : Except String 𝔸 :=
  match term with
  | te.inl term => Except.error "The structure of a term must have an injection only immediately inside a case"
  | te.inr term => Except.error "The structure of a term must have an injection only immediately inside a case"
  | te.case term name (te.inl term_l) (te.inr term_r) => do
    let l ← infer_type term_l
    let r ← infer_type term_r
    return 𝔸.sum l r
  | te.case term name (te.inr term_r) (te.inl term_l) => do
    let l ← infer_type term_l
    let r ← infer_type term_r
    return 𝔸.sum l r
  | te.case term name term_l term_r => do
    let l ← infer_type term_l
    let r ← infer_type term_r
    if (l == r) then pure r else Except.error "the types of the case arm don't match"
  | te.unit => pure 𝔸.unit
  | te.prod term_l term_r => do
    let l ← infer_type term_l
    let r ← infer_type term_r
    return 𝔸.prod l r
  | te.πₗ term => do
    let type ← infer_type term
    match type with
      | 𝔸.prod l r => return l
      | _  => Except.error "Projection on non product type"
  | te.πᵣ term => do
    let type ← infer_type term
    match type with
      | 𝔸.prod l r => return r
      | _  => Except.error "Projection on non product type"
  | te.var name type => pure type
  | te.ret term => infer_type term
  | te.lt name term => infer_type term
  | te.sample term => do
    let p_type ← infer_type term
    match p_type with
      | 𝔸.P type => return type
      | _ => Except.error "sample can only be done on a probability distribution"
  | te.score term => do
    let type ← infer_type term
    if (type == 𝔸.R) then pure 𝔸.unit else Except.error "score must be provided type ℝ"
  | te.normalize term => do
    let type ← infer_type term
    return 𝔸.sum (𝔸.sum (𝔸.prod 𝔸.R (𝔸.P type)) 𝔸.unit) 𝔸.unit

-- def measure_iunion (ι : Type*) (f: ι → Σ T: Type, MeasurableSpace T) :
--   MeasurableSpace T₁ ⊕ T₂ := sorry


-- marked as noncomputable because of Giry
-- noncomputable def type_denote' (ty : 𝔸) : Σ (T: Type), MeasurableSpace T :=
--   match ty with
--   | 𝔸.R => ⟨ℝ, borel ℝ⟩
--   | 𝔸.P ty' =>
--     let ⟨ty, _⟩ := type_denote' ty'
--     let foo := MeasCat.Giry.obj (MeasCat.of ty)
--     ⟨foo, foo.str⟩
--   | 𝔸.unit => ⟨PUnit, PUnit.instMeasurableSpace⟩ -- unit
--   | 𝔸.prod ty₁' ty₂' =>
--     let ⟨ty₁, _⟩ := type_denote' ty₁'
--     let ⟨ty₂, _⟩ := type_denote' ty₂'
--     ⟨ty₁ × ty₂, (inferInstance : MeasurableSpace (ty₁ × ty₂))⟩
--   | 𝔸.sum ty₁' ty₂' =>
--     let ⟨ty₁, _⟩ := type_denote' ty₁'
--     let ⟨ty₂, _⟩ := type_denote' ty₂'
--     ⟨ty₁ ⊕ ty₂, (inferInstance : MeasurableSpace (ty₁ ⊕ ty₂))⟩

-- noncomputable def type_denote (ty' : 𝔸) : MeasCat :=
--   let ⟨ty, _⟩ := type_denote' ty'
--   MeasCat.of ty

noncomputable def type_denote (ty : 𝔸) : MeasCat :=
  match ty with
  | 𝔸.R => MeasCat.of ℝ
  | 𝔸.P ty' => MeasCat.Giry.obj (type_denote ty')
  | 𝔸.unit => MeasCat.of PUnit
  | 𝔸.prod ty₁' ty₂' =>
    let ty₁ := type_denote ty₁'
    let ty₂ := type_denote ty₂'
    MeasCat.of (ty₁ × ty₂)
  | 𝔸.sum ty₁' ty₂' =>
    let ty₁ := type_denote ty₁'
    let ty₂ := type_denote ty₂'
    MeasCat.of (ty₁ ⊕ ty₂)

def Realizes (t : 𝔸) (T : Type*) := type_denote t ≃ T
-- ℝ ≃ ℝ
def realize_r : Realizes 𝔸.R ℝ := Equiv.refl ℝ
def realize_unit : Realizes 𝔸.unit PUnit := Equiv.refl PUnit


  -- MeasCat.isoOfEquiv (Equiv.refl ℝ)

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

abbrev context := List (var × 𝔸)

noncomputable def denote_context (vs : context) :=
  (type_prod ((List.map (fun (_, c) ↦ (type_denote c)) vs)))


-- TODO how to use loogle to find this if it exists?
/-- Returns `true` on `some x` and `false` on `none`. -/
@[inline] def Except.isError {ε α : Type*} (e : Except ε α) : Bool := not e.isOk

/--
TODO what does this syntax mean?
How does the other branch not need to be mentioned
Extracts the value from an option that can be proven to be `some`.
-/
@[inline] def Except.get {ε α : Type*} : (o : Except ε α) → Except.isOk o → α
  | Except.ok x, _ => x

abbrev well_typed_term := { term: te // (infer_type term).isOk }
-- Σ term: te, ( (infer_type term).isOk = true : Prop)
def get_type (wtt : well_typed_term) :=
  (infer_type wtt.1).get wtt.2

-- denote_term (term: te) (T : Type*) (Realizes (infer_term term) T)

def denote (vs : context) (wtt : well_typed_term) : Except String
  (denotation_ty (denote_context vs) (type_denote <| get_type wtt)) :=
  match h: wtt.1 with
  -- simplify this its awful
  | te.inl foo =>
    have h : False := by
      have fpp : ¬(infer_type (wtt.1)).isOk := by
        simp [h, infer_type, Except.isOk, Except.toBool]
      have fpp' : (infer_type wtt).isOk := wtt.2
      absurd fpp'
      exact fpp
    nomatch h

  -- simplify this its awful
  | te.inr foo =>
    have h : False := by
      have fpp : ¬(infer_type (wtt.1)).isOk := by
        simp [h, infer_type, Except.isOk, Except.toBool]
      have fpp' : (infer_type wtt).isOk := wtt.2
      absurd fpp'
      exact fpp
    nomatch h

  -- | case: te → var → te → te → te
  | te.unit =>
    -- let foo : (denote_context vs) → PUnit := (fun x ↦ PUnit.unit)
    -- let foo₃ : get_type wtt = 𝔸.unit := by simp only [h, get_type];rfl
    -- let foo'' : type_denote (get_type wtt) = PUnit := by
    --   simp only [foo₃, type_denote]--;sorry--rfl
    --   -- sorry
    -- let foo' : {f : (denote_context vs) → PUnit // Measurable f}
    --   := ⟨foo, by measurability⟩

    let foo₄ : {f : (denote_context vs) → type_denote (get_type wtt) // Measurable f} := by
      sorry
      --rw [foo'']
    Except.ok (Sum.inl foo₄)
  -- | prod: te → te → te
  -- | πₗ : te → te
  -- | πᵣ : te → te
  -- -- | f(t)
  -- | var: var → 𝔸 → te
  -- | ret: te → te -- return(t)
  -- | lt: var → te → te -- let x = t in u
  -- | sample: te → te
  -- | score: te → te
  -- | normalize: te → te
  | everything => sorry
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
