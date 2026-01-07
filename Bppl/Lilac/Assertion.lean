import Mathlib.MeasureTheory.Category.MeasCat

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

import Bppl.Lilac.KRM
/-!
Will need the subtly different types of objects (in the semantic domain) that variables that
variables can be interpreted to, to be defined, as certain types are allowed to be used in
connectives of Lilac.

Each of these variables (terms) will need to be interpreted under an environment.

Use `env` for the values and `ctx` for the types of these values.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
universe u v
-- Primitives
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons

notation "[" "]" => HList.nil

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | a::as, .tail h => as.get h

-- Define the various kinds of measurable fucntions we'll have to deal with
-- Fig 4. in Lilac paper, but why do we need that? For example `own E` is an assertion
-- which requires the definition of `E` as in `T-RANDE`

#check MeasCat

/- Here are we are parametric over the denotation of types in APPL -/

-- abbrev RV (A : Type) [MeasurableSpace A] := HList β αs →

open Iris.BI Iris

abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop

-- Instantiate basic connectives in BI

instance instBIBase {α : Type*} [nonempty : Nonempty α] : BIBase (PROP α ) where
  Entails P Q      := ∀ σ, P σ → Q σ
  emp            σ := σ = 1
  pure φ         _ := φ
  and P Q        σ := P σ ∧ Q σ
  or P Q         σ := P σ ∨ Q σ
  imp P Q        σ := P σ → Q σ
  sForall Ψ      σ := ∀ p, Ψ p → p σ
  sExists Ψ      σ := ∃ p, Ψ p ∧ p σ
  sep P Q        σ := ∃ σ1 σ2 : PSp α, σ1 • σ2 = some σ ∧ P σ1 ∧ Q σ2
  wand P Q       σ := ∀ σ' : PSp α, (h : (σ • σ').isSome) → P σ' → Q ((σ • σ').get h)
  -- could we do better than this? Identify what more is persistent/affine
  -- wasn't BaSL partially affine? What does that mean?
  persistently P _ := P 1
  later P        σ := P σ -- there is no step indexing

instance {α : Type*} [nonempty : Nonempty α] : COFE (PROP α) := COFE.ofDiscrete Eq equivalence_eq

instance instBI {α : Type*} [nonempty : Nonempty α] : BI (PROP α) where
  equiv_iff := sorry
  entails_preorder := sorry
  and_ne := sorry
  or_ne := sorry
  imp_ne := sorry
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := sorry
  wand_ne := sorry
  persistently_ne := sorry
  later_ne := sorry
  pure_intro := sorry
  pure_elim' := sorry
  and_elim_l := sorry
  and_elim_r := sorry
  and_intro := sorry
  or_intro_l := sorry
  or_intro_r := sorry
  or_elim := sorry
  imp_intro := sorry
  imp_elim := sorry
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := sorry
  emp_sep := sorry
  sep_symm := sorry
  sep_assoc_l := sorry
  wand_intro := sorry
  wand_elim := sorry
  persistently_mono := sorry
  persistently_idem_2 := sorry
  persistently_emp_2 := sorry
  persistently_and_2 := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l := sorry
  persistently_and_l := sorry
  later_mono := sorry
  later_intro := sorry
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := sorry
  later_persistently := sorry
  later_false_em := sorry
