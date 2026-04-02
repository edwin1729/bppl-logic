import Iris.BI.BIBase
import Iris.BI
import Iris.BI.Classes
import Iris.ProofMode

import Bppl.Lilac.Assertion

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Iris.BI.BIBase LProp Iris.BI Appl.Denotation

/- Almost Surely EQual-/
namespace Aseq

variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]
{ds : List TyDet} {rs : List TyRand} {A : TyRand}

-- Appendix B.13 from Lilac paper
lemma refl (E₁ : ValRand ds rs A) : iprop( ⊢ E₁ ≗ E₁) := sorry
lemma symm (E₁ E₂ : ValRand ds rs A) : iprop(E₁ ≗ E₂ ⊢ E₂ ≗ E₁) := sorry
lemma trans (E₁ E₂ E₃ : ValRand ds rs A) : iprop(E₁ ≗ E₂ ∧ E₂ ≗ E₃ ⊢ E₁ ≗ E₃) := sorry

-- Appendix B.15 from Lilac paper
lemma and_aseq_iff_sep_aseq (P : LProp ds rs) (E₁ E₂ : ValRand ds rs A) :
    iprop(P ∧ (E₁ ≗ E₂) ⊣⊢ P ∗ (E₁ ≗ E₂)) :=
  sorry

-- Maybe the definition of persistently could be changed inspired by the requirements of
-- this proof obligation
/-- Appendix B.16 from Lilac paper -/
instance aseq_persisitent (E₁ E₂ : ValRand ds rs A) : Persistent iprop(E₁ ≗ E₂) where
  persistent := sorry

/-- Appendix B.17 from Lilac paper -/
lemma transfer_own (E₁ E₂ : ValRand ds rs A) : iprop(own E₁ ∧ E₁ ≗ E₂ ⊢ own E₂) := sorry

/-- Appendix B.17 from Lilac paper -/
lemma transfer_dist (E₁ E₂ : ValRand ds rs A) (ν : DistDet ds A) :
    iprop(E₁ ∼ ν ∧ E₁ ≗ E₂ ⊢ E₂ ∼ ν)
  := sorry

-- TODO B.18 what does `own(F[E₁], F[E₂])` mean in the paper?

-- B.19, don't think this is needed

-- Appendix B.22 from Lilac paper

end Aseq
namespace WP
open ProbabilityTheory MeasureTheory Appl PMF NNReal
-- variable {TyDet TyRand : Type} [td : Denotational TyDet] [tdm : DenotationalMeas TyRand]
variable {ds : List Ty} {rs : List Ty} {A ty₁ ty₂ : Ty}
noncomputable section

-- TODO: It is unclear how to express the substitution of `wp_ret`. Just a function?

/-- The semantic (native lean) uniform distribution in the interval [0,1]. -/
def unif01_sem : HList (⟪·⟫) ds → Measure ℝ := fun _ ↦ uniformOn (Set.Icc 0 1)

def ber_sem (p : ℝ≥0) (hp : p ≤ 1) : HList (⟪·⟫) ds → Measure Bool :=
  fun _ ↦ (bernoulli p hp).toMeasure

/-- Variable at the head of the random environment list. -/
def fst_rand : ValRand ds (A::rs) A :=
  fun _d_env ↦ ⟨fun r_env ↦ r_env.get .head , List.TProd.measurable_get .head⟩

lemma wp_unif (Q : LProp ds (Ty.real :: rs)) :
    forall_rv Ty.real iprop(fst_rand ∼ unif01_sem -∗ Q) ⊢ wp ⦃Term.unif01⦄ Q :=
  sorry

lemma wp_flip (p : ℝ≥0) (hp : p ≤ 1) (Q : LProp ds (Ty.bool :: rs)) :
    forall_rv Ty.bool iprop(fst_rand ∼ (ber_sem p hp) -∗ Q) ⊢ wp ⦃Term.flip p hp⦄ Q :=
  sorry

-- lemma wp_let (M : Term rs (.G ty₁)) (N : Term (ty₁ :: rs) (.G ty₂))
-- Term ctx (.G ty₁) → Term (ty₁ :: ctx) (.G ty₂) → Term ctx (.G ty₂)

end
end WP
