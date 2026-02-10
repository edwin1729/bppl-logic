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
abbrev detVal (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → ⟦A⟧)

/-- Random Value -/
abbrev randVal (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ ⟦A⟧)

/-- Deterministic distribution -/
abbrev detDist (ds : List TyDet) (A : TyRand) := (HList (⟦·⟧) ds → Measure ⟦A⟧)

/-- Random distribution -/
abbrev randDist (ds : List TyDet) (rs : List TyRand) (A : TyRand) :=
  (HList (⟦·⟧) ds → List.TProd (⟦·⟧) rs -m→ Measure ⟦A⟧)

-- The Hilbert cube instantiation is used in giving the semantics (satisfiability relation)
abbrev HC := ℕ → Set.Icc (0:ℝ) 1

/-- Todo add finite footprint condition -/
abbrev RV (A : Type) [MeasurableSpace A] := HC -m→ A

/-- Lilac propositions -/
abbrev lProp (ds : List TyDet) (rs : List TyRand) :=
  HList (⟦·⟧) ds → RV (List.TProd (⟦·⟧) rs) → PSp HC → Prop

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
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ P, Ψ P → P γ D φ

def sExists (Ψ : lProp ds rs → Prop)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ P, Ψ P → P γ D φ

def pure (P : Prop) : lProp ds rs := fun _ _ _ ↦ P
def emp : lProp ds rs := fun _ _ φ ↦ φ = 1

def top : lProp ds rs := fun _ _ _ ↦ True
def bot : lProp ds rs := fun _ _ _ ↦ False

def and (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  P γ D φ ∧ Q γ D φ
def or (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  P γ D φ ∨ Q γ D φ
def imp (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φ', φ ≤ φ' → P γ D φ' → Q γ D φ'
def sep (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ φ₁ φ₂ : PSp HC, φ₁ ⋆ φ₂ ≤ some φ ∧ P γ D φ₁ ∧ Q γ D φ₂
def wand (P Q : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φp, ∃ φq, φp ⋆ φ = some φq ∧ (P γ D φp → Q γ D φq)

def persistently (P : lProp ds rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (_ : PSp HC) : Prop :=
  P γ D 1

-- is it a problem that only types at the head of the list can be quantified over?
def «forall» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ x : ⟦d⟧, P (x :: γ) D φ
def «exists» (d : TyDet) (P : lProp (d :: ds) rs)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ x : ⟦d⟧, P (x :: γ) D φ
def forall_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ X : RV ⟦r⟧, P γ (X ; D) φ
def exists_rv (r : TyRand) (P : lProp ds (r :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∃ X : RV ⟦r⟧, P γ (X ; D) φ

def own (E : randVal ds rs A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  Measurable[φ.1] ((E γ).1 ∘ D.1)

def dist (E : randVal ds rs A) (μ : detDist ds A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  Measurable[φ.1] ((E γ).1 ∘ D.1) ∧ μ γ = .bind φ.2 (fun ω ↦ Measure.dirac (E γ (D ω)))

-- confirm if (X₁, X₂)⁻¹ (A) = X₁⁻¹ (A) ∪ X₂⁻¹ (A) ∪
-- Do we need different types A₁ and A₂ (what's the use of almost sure equality)
-- | expectation -- skip this for now becase TyRand doesn't claim to have a type whose
-- denotation is ℝ
def eq (E₁ E₂ : randVal ds rs A)
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  let X₁ := (E₁ γ).1 ∘ D.1
  let X₂ := (E₂ γ).1 ∘ D.1
  -- let F := {ω | X₁ ω = X₂ ω}
  sorry --: randVal ds rs A → randVal ds rs A → Term ds rs -- almost sure equality

-- consider just taking another PSp instead of μ, if it might simplify proof later
def wp (M : randDist ds rs A) (Q : lProp ds (A :: rs))
    (γ : HList (⟦·⟧) ds) (D : RV (List.TProd (⟦·⟧) rs)) (φ : PSp HC) : Prop :=
  ∀ φ_fr : PSp HC, ∀ μ : ProbabilityMeasure HC,
  φ_fr ⋆ φ ≤ some (PSp.mk _ μ.1 μ.2) → ∀ {rs' : List TyRand},
  ∀ D' : RV (List.TProd (⟦·⟧) (rs' ++ rs)),
  ∃ X : RV ⟦A⟧, ∃ φ' : PSp HC,
  ∃ μ' : ProbabilityMeasure HC, φ_fr ⋆ φ' ≤ some (PSp.mk _ μ'.1 μ'.2) ∧
  (Measure.bind μ.1 (fun ω ↦ Measure.bind (M γ (D ω)) (fun v ↦ Measure.dirac (D' ω, D ω, v)))) =
    (Measure.bind μ'.1 (fun ω ↦ Measure.dirac (D' ω, D ω, X ω))) ∧
  Q γ (X ; D) φ'

end lProp

/- Satisfaction relation: `(γ, D, φ)⊨ P` means `P` holds under deterministic env `γ`,
    random env `D`, and resource `φ` -/
-- notation:50 "(" γ ", " D ", " φ ")⊨ " P => Assertion.denote P γ D φ

open Iris.BI Iris

-- abbrev PROP (α : Type*) [nonempty : Nonempty α] := PSp α → Prop

-- Instantiate basic connectives in BI

instance instBIBase {ds : List TyDet} {rs : List TyRand} : BIBase (lProp ds rs) where
  Entails P Q    := ∀ γ D φ, P γ D φ → Q γ D φ
  emp            := .emp
  pure           := .pure
  and            := .and
  or             := .or
  imp            := .imp
  sForall        := .sForall
  sExists        := .sExists
  sep            := .sep
  wand           := .wand
  -- could we do better than this? Identify what more is persistent/affine
  -- wasn't BaSL partially affine? What does that mean?
  persistently   := .persistently
  later P        := P -- there is no step indexing

instance {ds : List TyDet} {rs : List TyRand} : COFE (lProp ds rs) :=
  COFE.ofDiscrete Eq equivalence_eq

instance instBI {ds : List TyDet} {rs : List TyRand} : BI (lProp ds rs) where
  equiv_iff {P Q} := ⟨
    fun h : P = Q => h ▸ ⟨refl, refl⟩,
    fun ⟨h₁, h₂⟩ => by ext γ D φ; exact ⟨h₁ γ D φ, h₂ γ D φ⟩
  ⟩
  entails_preorder := sorry -- by infer_instance

  and_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  or_ne           := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  imp_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  sep_ne          := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  wand_ne         := ⟨by rintro _ _ _ rfl _ _ rfl; rfl⟩
  persistently_ne := ⟨by rintro _ _ _ rfl; rfl⟩
  later_ne        := ⟨by rintro _ _ _ rfl; rfl⟩
  sForall_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl
  sExists_ne {_ P Q} h := liftRel_eq.1 h ▸ rfl

  pure_intro h _ _ := h
  pure_elim' h_φP σ h_φ := h_φP h_φ σ ⟨⟩

  and_elim_l := by
    intros
    simp only [BI.Entails, BI.and]
    intro _ h
    exact h.left
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h
    exact h.right
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR σ h_P
    constructor
    · exact h_PQ σ h_P
    · exact h_PR σ h_P

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR σ h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR σ h_P
    case inr h_Q =>
      exact h_QR σ h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ h_P h_Q
    exact h_PQR σ ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    exact h_PQR σ h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ σ h_P p hp
    exact h_PΨ p hp σ h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact ⟨p, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp σ h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _ h_PQ h_P'Q' _ ⟨σ₁, σ₂, h_union, h_disjoint, h_P, h_P'⟩
    apply Exists.intro σ₁
    apply Exists.intro σ₂
    constructor
    · exact h_union
    constructor
    · exact h_disjoint
    constructor
    · exact h_PQ σ₁ h_P
    · exact h_P'Q' σ₂ h_P'
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp]
    intro _ ⟨σ₁, σ₂, h_union, _, h_emp, h_P⟩
    rw [h_emp] at h_union
    rw [← empty_union] at h_union
    rw [h_union]
    exact h_P
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp]
    intro σ h_P
    apply Exists.intro ∅
    apply Exists.intro σ
    constructor
    · exact empty_union
    constructor
    · exact empty_disjoint
    constructor
    · rfl
    · exact h_P
  sep_symm := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ ⟨σ₁, σ₂, h_union, h_disjoint, h_P, h_Q⟩
    apply Exists.intro σ₂
    apply Exists.intro σ₁
    constructor
    · rw [union_comm] ; exact h_union
    constructor
    · rw [disjoint_comm] ; exact h_disjoint
    constructor
    · exact h_Q
    · exact h_P
  sep_assoc_l := by
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _
      ⟨σ₁, σ₂, h_union₁₂, h_disjoint₁₂, ⟨σ₃, σ₄, h_union₃₄, h_disjoint₃₄, h_P, h_Q⟩, h_R⟩
    apply Exists.intro σ₃
    apply Exists.intro (σ₄ ∪ σ₂)
    constructor
    · rw [h_union₃₄] at h_union₁₂
      rw [← union_assoc]
      exact h_union₁₂
    constructor
    · apply disjoint_union
      · exact h_disjoint₃₄
      · rw [h_union₃₄] at h_disjoint₁₂
        let h_disjoint := disjoint_assoc h_disjoint₁₂ h_disjoint₃₄
        exact h_disjoint.left
    constructor
    · exact h_P
    apply Exists.intro σ₄
    apply Exists.intro σ₂
    constructor
    · rw [union_comm]
    constructor
    · rw [h_union₃₄] at h_disjoint₁₂
      let h_disjoint := disjoint_assoc h_disjoint₁₂ h_disjoint₃₄
      exact h_disjoint.right
    constructor
    · exact h_Q
    · exact h_R

  wand_intro := by
    simp only [BI.Entails, BI.wand, BI.sep]
    intro _ _ _ h_PQR σ h_P σ' h_disjoint h_Q
    apply h_PQR (σ ∪ σ')
    apply Exists.intro σ
    apply Exists.intro σ'
    constructor
    · rfl
    constructor
    · exact h_disjoint
    constructor
    · exact h_P
    · exact h_Q
  wand_elim := by
    simp only [BI.Entails, BI.wand, BI.sep]
    intro _ _ _ h_PQR _ ⟨σ, σ', h_union, h_disjoint, h_P, h_Q⟩
    rw [h_union]
    exact h_PQR σ h_P σ' h_disjoint h_Q

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ _ h_P
    exact h_PQ ∅ h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro _ _
    simp
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ h
    exact h
  persistently_sExists_1 := by
    simp only [BI.Entails, BI.persistently, BI.exists]
    intro _ _ ⟨p, hp, h⟩
    exact ⟨_, ⟨_, rfl⟩, hp, h⟩
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ _ ⟨_, _, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
    intro _ _ σ ⟨h_P, h_Q⟩
    apply Exists.intro ∅
    apply Exists.intro σ
    constructor
    · exact empty_union
    constructor
    · exact empty_disjoint
    constructor
    · exact h_P
    · exact h_Q

  later_mono := id
  later_intro _ := id
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ => id, fun _ => id⟩
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em _ h := .inr fun _ => h
