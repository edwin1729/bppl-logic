import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Iris.BI.BIBase
import Iris.BI
import Iris.Algebra.OFE
import Iris.Std.Equivalence

import Bppl.Lilac.KRM
import Bppl.Lilac.Appl

set_option autoImplicit true
set_option relaxedAutoImplicit true


/- Here are we are parametric over the denotation of types in APPL.
To remain general, we assume there are two kinds of types in APPL,
whose dentotation is 1) `Meas` 2) `Set`

(Though in our actual definition of APPL, all types have denotation in `Meas` and every element
of `Meas` is also in `Set`)-/

/- Questions

-- Do we really need a measurable space on the domain of D and D to be measurable?
-- and why do we need finite footprint?o

-- Interesting that measure on the hilbert cube is not uniform, or is it?
-- for σ-algebra with finite footprint at least??

-/

open MeasureTheory

/- `TyRand` and `TyDet` need to have a denotation function. Additionally `TyRand`'s
denotation must have a measurable space structure -/
variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]

/-- Deterministic Value -/
abbrev ValDet (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → ⟦A⟧)

/-- Random Value -/
abbrev ValRand (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ ⟦A⟧)

/-- Deterministic distribution -/
abbrev DistDet (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → Measure ⟦A⟧)

/-- Random distribution -/
abbrev DistRand (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ Measure ⟦A⟧)

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

/-- Todo add finite footprint condition -/
abbrev RV (A : Type) [MeasurableSpace A] := HC -m→ A

abbrev EnvDet (ds : List TyDet) := HList (⟦·⟧) ds
abbrev EnvRand (rs : List TyRand) := RV (List.TProd (⟦·⟧) rs)

/-- Lilac propositions -/
abbrev lProp (ds : List TyDet) (rs : List TyRand) :=
  EnvDet ds → EnvRand rs → PSp HC → Prop

-- Using `MeasurableSpace.pi`
instance : MeasurableSpace HC := inferInstance

namespace MeasurableFunc
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def comp (g : β -m→ γ) (f : α -m→ β)
  : α -m→ γ := ⟨g.1 ∘ f.1, Measurable.comp g.2 f.2⟩

notation g " ∘ " f => comp g f

def fun_prod (f : α -m→ β) (g : α -m→ γ) : α -m→ β × γ :=
  ⟨fun a ↦ (f a, g a), Measurable.prod f.2 g.2⟩

notation x " ; " xs => fun_prod x xs

end MeasurableFunc

namespace lProp

-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand}

-- The idea is to get a singleton set of a ∀ or ∀ᵣᵥ assertion as input and the same term
-- as output (when taking denotation). So the ds and rs type indices are the same
def sForall (Ψ : lProp ds rs → Prop)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ P, Ψ P → P γ D Ω

def sExists (Ψ : lProp ds rs → Prop)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ P, Ψ P ∧ P γ D Ω

def pure (φ : Prop) : lProp ds rs := fun _ _ _ ↦ φ
def emp : lProp ds rs := fun _ _ Ω ↦ Ω = 1

def top : lProp ds rs := fun _ _ _ ↦ True
def bot : lProp ds rs := fun _ _ _ ↦ False

def and (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  P γ D Ω ∧ Q γ D Ω
def or (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  P γ D Ω ∨ Q γ D Ω
def imp (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ω', Ω ≤ Ω' → P γ D Ω' → Q γ D Ω'
def sep (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ Ω₁ Ω₂ : PSp HC, Ω₁ ⋆ Ω₂ ≤ some Ω ∧ P γ D Ω₁ ∧ Q γ D Ω₂
def wand (P Q : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ωp, ∃ Ωq, Ωp ⋆ Ω = some Ωq ∧ (P γ D Ωp → Q γ D Ωq)

-- could we do better than this? Identify what more is persistent/affine
-- wasn't BaSL partially affine? What does that mean?
def persistently (P : lProp ds rs)
    (γ : EnvDet ds) (D : EnvRand rs) (_ : PSp HC) : Prop :=
  P γ D 1
-- there is no step indexing
def later (P : lProp ds rs) : lProp ds rs := P

-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ x : ⟦d⟧, P (x :: γ) D Ω
def «exists» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ x : ⟦d⟧, P (x :: γ) D Ω
def forall_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ X : RV ⟦r⟧, P γ (X ; D) Ω
def exists_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∃ X : RV ⟦r⟧, P γ (X ; D) Ω

def own (E : ValRand ds rs A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  Measurable[Ω.1] ((E γ).1 ∘ D.1)

def dist (E : ValRand ds rs A) (μ : DistDet ds A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  Measurable[Ω.1] ((E γ).1 ∘ D.1) ∧ μ γ = .bind Ω.2 (fun ω ↦ Measure.dirac (E γ (D ω)))

-- confirm if (X₁, X₂)⁻¹ (A) = X₁⁻¹ (A) ∪ X₂⁻¹ (A) ∪
-- Do we need different types A₁ and A₂ (what's the use of almost sure equality)
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ
def eq (E₁ E₂ : ValRand ds rs A)
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  let X₁ := (E₁ γ).1 ∘ D.1
  let X₂ := (E₂ γ).1 ∘ D.1
  -- let F := {ω | X₁ ω = X₂ ω}
  sorry --: randVal ds rs A → randVal ds rs A → Term ds rs -- almost sure equality

-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : DistRand ds rs A) (Q : lProp ds (A :: rs))
    (γ : EnvDet ds) (D : EnvRand rs) (Ω : PSp HC) : Prop :=
  ∀ Ω_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
  Ω_fr ⋆ Ω ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
  ∃ X : RV ⟦A⟧, ∃ Ω' : PSp HC,
  ∃ μ' : ProbabilityMeasure HC, Ω_fr ⋆ Ω' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q γ (X ; D) Ω'

end lProp

/- Satisfaction relation: `(γ, D, Ω)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `Ω` -/
-- notation:50 "(" γ ", " D ", " Ω ")⊨ " P => Assertion.denote P γ D Ω

namespace BI
open Iris.BI Iris
-- ds: deterministic context, rs: random variable context
variable {ds : List TyDet} {rs : List TyRand}

-- abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop

-- Instantiate basic connectives in BI

instance instBIBase : BIBase (lProp ds rs) where
  Entails P Q    := ∀ γ D Ω, P γ D Ω → Q γ D Ω
  emp            := .emp
  pure           := .pure
  and            := .and
  or             := .or
  imp            := .imp
  sForall        := .sForall
  sExists        := .sExists
  sep            := .sep
  wand           := .wand
  persistently   := .persistently
  later          := .later

instance : Std.Preorder (Entails (PROP := lProp ds rs)) where
  refl := by
    simp only [BI.Entails]
    intro _ _ _ _ h
    exact h
  trans := by
    simp only [BI.Entails]
    intro _ _ _ h_xy h_yz γ D Ω h_x
    apply h_yz γ D Ω
    apply h_xy γ D Ω
    exact h_x

instance {ds : List TyDet} {rs : List TyRand} : COFE (lProp ds rs) :=
  COFE.ofDiscrete Eq equivalence_eq

/-- These proofs have been ported from the Iris-lean to the classical separation logic,
modified as necessary. The similarities between the two logics is the lack of step-indexing
and general similarity in non-spatial axioms -/
instance instBI {ds : List TyDet} {rs : List TyRand} : BI (lProp ds rs) where
  entails_preorder := by infer_instance
  equiv_iff {P Q} := ⟨
    fun h : P = Q => h ▸ ⟨fun _ _ _ φ ↦ φ, fun _ _ _ φ ↦ φ⟩,
    fun ⟨h₁, h₂⟩ => by ext γ D Ω; exact ⟨h₁ γ D Ω, h₂ γ D Ω⟩
  ⟩
  and_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  or_ne           := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  imp_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  sep_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  wand_ne         := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  persistently_ne := ⟨by rintro _ _ _ rfl; rfl⟩
  later_ne        := ⟨by rintro _ _ _ rfl; rfl⟩
  sForall_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl
  sExists_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl

  pure_intro h _ _ _ _ := h
  pure_elim' h_φP γ D Ω h_φ := h_φP h_φ γ D Ω ⟨⟩

  and_elim_l := by
    intros
    simp only [BI.Entails, BI.and]
    intro _ _ _ h
    exact h.left
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ _ _ h
    exact h.right
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR γ D Ω h_P
    constructor
    · exact h_PQ γ D Ω h_P
    · exact h_PR γ D Ω h_P

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR γ D Ω h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR γ D Ω h_P
    case inr h_Q =>
      exact h_QR γ D Ω h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR γ D Ω h_P Ω' Ω_le_Ω' h_Q
    sorry -- TODO ≤ (actually the below case is the problem)
    -- exact h_PQR γ D Ω ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR γ D Ω ⟨h_P, h_Q⟩
    sorry -- TODO ≤
    -- exact h_PQR γ D Ω h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ γ D Ω h_P p hp
    exact h_PΨ p hp γ D Ω h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp _ _ _ h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp _ _ _ h_Ψ
    exact ⟨p, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ γ D Ω ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp γ D Ω h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ h_PQ h_P'Q' γ D Ω ⟨Ω₁, Ω₂, h_Ω, h_P, h_P'⟩
    use Ω₁, Ω₂
    exact ⟨h_Ω, h_PQ γ D Ω₁ h_P, h_P'Q' γ D Ω₂ h_P'⟩
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp]

    intro _ _ _ ⟨σ₁, σ₂, h_Ω, h_emp, h_P⟩
    -- Ω
    -- rw [h_emp] at h_union
    rw [h_emp, Pcm.one_mul, Option.some_le_some] at h_Ω
    sorry -- TODO ≤
    -- rw [← h_Ω]
    -- exact h_Ω ▸ h_P
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp]
    sorry -- TODO ≤ (This is actually provable. Just inverse of the above broken case
    -- so skipped)
  sep_symm := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ _ ⟨Ω₁ , Ω₂, h_union, h_P, h_Q⟩
    use Ω₂, Ω₁
    rw [Pcm.comm]
    exact ⟨h_union, h_Q, h_P⟩
  sep_assoc_l := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ _ _
      ⟨Ω₁₂, Ω₃, h_Ω₁₂₃ₗ, ⟨Ω₁, Ω₂, h_Ω₁₂, h_P₁, h_P₂⟩, h_P₃⟩
    use Ω₁
    -- usage of Pcm.assoc is obstructed by ≤
    sorry  -- Todo ≤

  -- suspect these might change due to ≤
  wand_intro := sorry
  wand_elim := sorry

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ γ D _ h_P
    exact h_PQ γ D 1 h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro γ D Ω P
    rw [lProp.emp] at P
    rw [lProp.persistently, lProp.emp]
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ _ _ h
    exact h
  persistently_sExists_1 := by
    simp only [BI.Entails, BI.persistently, BI.exists]
    intro _ _ _ _ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ _ _ _ ⟨_, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
    intro _ _ _ _ σ ⟨h_P, h_Q⟩
    apply Exists.intro 1
    apply Exists.intro σ
    constructor
    · rw [Pcm.one_mul, Option.some_le_some]
    constructor
    · exact h_P
    · exact h_Q

  later_mono := id
  later_intro _ _ _ := id
  later_sForall_2 {Φ} γ D Ω P := by
    simp only [later, lProp.later, sForall, lProp.sForall] -- for clarity, can delete
    intro Q h_Q
    let foo := P Q
    apply foo
    use Q
    simp [BI.pure, later, lProp.later]
    ext γ D Ω
    constructor
    ·
      intro P'
      exact P' Ω (le_refl _) h_Q
    ·
      intro q Ω' h_Ω' P'
      sorry -- TODO ≤ (require that bigger )

  later_sExists_false _ _ _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ _ _ => id, fun _ _ _ => id⟩
  later_persistently := ⟨fun _ _ _ => id, fun  _ _ _ => id⟩
  later_false_em _ _ _ h := .inr fun _ _ _ => (by
    simp [later, lProp.later] at h
    sorry -- TODO ≤ :(
    -- exact h
  )

end BI
