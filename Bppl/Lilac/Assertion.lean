import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl
/-!
Will need the subtly different types of objects (in the semantic domain) that variables that
variables can be interpreted to, to be defined, as certain types are allowed to be used in
connectives of Lilac.

Each of these variables (terms) will need to be interpreted under an environment.

Use `env` for the values and `ctx` for the types of these values.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true


-- Define the various kinds of measurable fucntions we'll have to deal with
-- Fig 4. in Lilac paper, but why do we need that? For example `own E` is an assertion
-- which requires the definition of `E` as in `T-RANDE`

/- Here are we are parametric over the denotation of types in APPL.
To remain general, we assume there are two kinds of types in APPL,
whose dentotation is 1) `Meas` 2) `Set`

(Though in our actual definition of APPL, all types have denotation in `Meas` and every element
of `Meas` is also in `Set`)-/

-- TODO introduce notation for Measurable fns
-- TODO we might want to have an MList of types which are measurable, and specialize the development
-- here to use just that. Depends on how we would instantiate the types here come APPL.
-- For now I keep it verbose with casts like `(fun i => ↑(β i)) is`, keeping in mind the
-- direction of succinctness


-- instance instMeasurableProd : MeasurableSpace (MList β is) where
-- universe u₁ u₂
-- abbrev RV {β₁ : α₁ → Type u₁} {is : List α₁} -- The deterministic env
--     {β₂ : α₂ → Type u₂} {is' : List α₂} -- The probabilistic env which needs to be measurable
--     (A : Type) [MeasurableSpace A] :=
--   {f : ∀ a, }
  --HList β₁ is → A--{ f : HList β₂ is' → A // Measurable f }

-- attempt to at defining an Assertion. Plan: copy dependent de Brujin indicies
-- with "Term" being assertion and denotation being semantics as expected.


-- we're struggling to see how to couple the logic with the language. So let's tackle that
-- separately, and for the moment let

/- `TyRand` and `TyDet` need to have a denotation function. Additionally `TyRand`'s
dentoation must have a measurable space structure -/
variable {TyDet TyRand : Type} [Denotational TyDet] [DenotationalMeas TyRand]

-- Here Term means Assertion actually
inductive Term : List TyDet → List TyRand → Type
  -- | var   : Member ty ctx → Term ctx
  | bot : Term ds rs -- ds: deterministic context, rs: random variable context
  | and  : Term ds rs  → Term ds rs → Term ds rs
  | sep  : Term ds rs  → Term ds rs → Term ds rs
  | persistently  : Term ds rs  → Term ds rs
  | forall : Term (d :: ds) rs → Term ds rs
  -- | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  -- | let : Term ctx ty₁ → Term (ty₁ :: ctx) ty₂ → Term ctx ty₂
  | own {ds : List TyDet} {rs : List TyRand} {A : TyRand} :
      (HList (⟦·⟧) ds → {f : List.TProd (⟦·⟧) rs → ⟦A⟧ // Measurable f})
      → Term ds rs
-- ⊤ | ⊥ | 𝑃 ∧ 𝑄 | 𝑃 ∨ 𝑄 | 𝑃 → 𝑄 |
-- 𝑃 ∗ 𝑄 | 𝑃 −∗ 𝑄 | □ 𝑃 |
-- ∀𝑥:𝑆.𝑃 | ∃𝑥:𝑆.𝑃 | ∀rv𝑋 :𝐴.𝑃 | ∃rv𝑋 :𝐴.𝑃 |
-- 𝐸 ∼ 𝜇 | own 𝐸 | 𝐸 =as= 𝐸 | E[𝐸] = 𝑒 | wp(𝑀, 𝑋 :𝐴.𝑄)

-- now define semantics for these "Terms". Then use said semantics
-- in definition of `Entails`.

-- Haziest in my mind: 1) wp semantics 2) instantiations of `TyDet` and `TyRand`

-- does the order of parameters matter? For purposes of dependencies?
-- If not I would like it to be in the order γ → D → 𝒫 → P → Prop
-- for encoding the four way satisfiabilty relation: γ, D 𝒫 ⊨ P
variable {α : Type*} [nonempty : Nonempty α]


-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)

-- Hilbert Cube
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

-- Useing `MeasurableSpace.HC
instance : MeasurableSpace HC := inferInstance
-- ∧
open MeasureTheory

-- def RV (A : Type) [MeausurableSpace A] := {f : α → A // measurable }

-- This section was made originally to be used with `own E` or any other probability specfic
-- connectives. But we may not need this at all, since `Own E` is alway `True` if one is able
-- to construct an `E` in the first place!
section
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def MeasurableFunction.compose (g : MeasurableFunction β γ) (f : MeasurableFunction α β)
  : MeasurableFunction α γ := ⟨g.1 ∘ f.1, Measurable.comp g.2 f.2⟩

notation g " ∘ " f => MeasurableFunction.compose g f

end
-- `by coarser` might be a nice custom tactic name for dealing with those sorries
@[simp] noncomputable def Term.denote {ds : List TyDet} {rs : List TyRand} :
    Term ds rs → (σ : PSp HC) → HList (⟦·⟧) ds → {f : HC → List.TProd (⟦·⟧) rs // Measurable[σ.1] f } → Prop
  | bot, _, _, _  => False
  | and P Q, σ, γ, D => P.denote σ γ D ∧ Q.denote σ γ D
  -- Fill sorry with a lemma that `σ₁ ≤ σ` and `σ₂ ≤ σ`
  | sep P Q, σ, γ, D => ∃ σ₁ σ₂ : PSp HC, σ₁ • σ₂ ≤ some σ ∧ P.denote σ₁ γ ⟨D.1, Measurable.le sorry D.2⟩ ∧ Q.denote σ₂ γ ⟨D.1, Measurable.le sorry D.2⟩
  -- Fill sorry with ∀ σ : PSp α, 1.1 ≤ σ.1. In words, The sigma algebra of `1` is the least or coarsest
  | persistently P, _, γ, D => P.denote 1 γ ⟨D.1, Measurable.le (sorry) D.2⟩
  | «forall» P, σ, γ, D => ∀ x, P.denote σ (x :: γ) D
  -- We could just say `True` for the semantics of `own E`
  | own E, σ, γ, D => Measurable[σ.1] ((E γ).1 ∘ D.1) -- hmmm. Curiously, this must hold by construction!
  -- Our model using dependent types is doing much of the heavy lifting at the syntactic stage to begin with

/-- Satisfaction relation: `(γ, D, σ)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `σ` -/
notation:50 "(" γ ", " D ", " σ ")⊨ " P => Term.denote P γ D σ

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
