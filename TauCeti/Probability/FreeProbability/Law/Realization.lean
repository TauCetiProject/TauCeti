/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.Probability.FreeProbability.Law.FreeProduct

/-!
# Free realizations of compactly supported laws

Every family `(μ i)` of compactly supported probability measures on `ℝ` is the family of laws of
freely independent selfadjoint elements of a C⋆-probability space. The elements are the
coordinate functions `x ↦ x` in the commutative C⋆-algebras `C(supp μ i, ℂ)`, carried into the
reduced free product of these algebras with respect to the states `f ↦ ∫ f dμ i`; the
C⋆-probability space is the algebra of bounded operators on its GNS Hilbert space with the vacuum
vector state. The spectrum of each element lies in the support of its law.

Conversely, laws of free families do not depend on the realization: if two free families of
selfadjoint elements, possibly in different C⋆-algebras, have the same individual laws, then
every noncommutative polynomial in them that is selfadjoint has the same law in both. This is
the uniqueness of the free joint distribution transported to laws. Together these make the free
convolutions of compactly supported measures well defined.

## Main declarations

* `PositiveLinearMap.law_lift_eq_law_lift_of_jointDistribution_eq`: equal joint distributions
  give equal laws of selfadjoint polynomial evaluations.
* `TauCeti.IsFreelyIndependentElements.law_lift_eq_law_lift`: free families with equal individual
  laws give equal laws of selfadjoint polynomial evaluations.
* `TauCeti.exists_isFreelyIndependentElements_law_eq`: free realization of a family of compactly
  supported probability measures.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 6 and 12.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.5 and 3.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder

universe u

namespace PositiveLinearMap

variable {A B ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}

/-- Families with equal joint distributions, possibly in different C⋆-algebras, give the same
law to every noncommutative polynomial whose evaluations on both families are selfadjoint. -/
theorem law_lift_eq_law_lift_of_jointDistribution_eq {a : ι → A} {b : ι → B}
    (h : TauCeti.jointDistribution φ.toLinearMap a = TauCeti.jointDistribution ψ.toLinearMap b)
    {p : FreeAlgebra ℂ ι} (ha : IsSelfAdjoint (FreeAlgebra.lift ℂ a p))
    (hb : IsSelfAdjoint (FreeAlgebra.lift ℂ b p)) :
    law φ (FreeAlgebra.lift ℂ a p) = law ψ (FreeAlgebra.lift ℂ b p) :=
  (law_eq_law_iff_forall_apply_pow φ ψ ha hb).2 fun n => by
    simpa [← map_pow] using LinearMap.congr_fun h (p ^ n)

end PositiveLinearMap

namespace TauCeti

open PositiveLinearMap

/-- **Free families have realization-independent laws.** Let `a` and `b` be freely independent
families of selfadjoint elements for states `φ` and `ψ` on possibly different C⋆-algebras, with
`μ_{a i} = μ_{b i}` for every `i`. Then every noncommutative polynomial `p` whose evaluations on
both families are selfadjoint has the same law: `μ_{p(a)} = μ_{p(b)}`. -/
theorem IsFreelyIndependentElements.law_lift_eq_law_lift {A B ι : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ} {a : ι → A} {b : ι → B}
    (hfa : IsFreelyIndependentElements φ.toLinearMap a)
    (hfb : IsFreelyIndependentElements ψ.toLinearMap b) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : ∀ i, IsSelfAdjoint (b i))
    (hlaw : ∀ i, law φ (a i) = law ψ (b i)) {p : FreeAlgebra ℂ ι}
    (hpa : IsSelfAdjoint (FreeAlgebra.lift ℂ a p)) (hpb : IsSelfAdjoint (FreeAlgebra.lift ℂ b p)) :
    law φ (FreeAlgebra.lift ℂ a p) = law ψ (FreeAlgebra.lift ℂ b p) :=
  law_lift_eq_law_lift_of_jointDistribution_eq
    (hfa.jointDistribution_eq_of_forall_pow hfb hφ hψ fun i =>
      (law_eq_law_iff_forall_apply_pow φ ψ (ha i) (hb i)).1 (hlaw i)) hpa hpb

/-- **Free realization of compactly supported laws.** Every family `(μ i)` of compactly
supported probability measures on `ℝ` is the family of laws of freely independent selfadjoint
elements `a i` of a C⋆-algebra with a state `φ`, with the spectrum of each `a i` contained in the
support of `μ i`. -/
theorem exists_isFreelyIndependentElements_law_eq {I : Type u} (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : I → A), φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ (∀ i, law φ (a i) = μ i) ∧
          ∀ i, spectrum ℝ (a i) ⊆ (μ i).support := by
  have := fun i => isCompact_iff_compactSpace.1 (hμ i)
  exact ⟨FreeLawRealization.algebra μ, inferInstance, inferInstance, inferInstance,
    FreeLawRealization.state μ, FreeLawRealization.generator μ,
    FreeLawRealization.state_one μ, FreeLawRealization.isSelfAdjoint_generator μ,
    FreeLawRealization.isFreelyIndependentElements_generator μ,
    FreeLawRealization.law_generator μ,
    fun i => (FreeLawRealization.spectrum_generator μ i).subset⟩

end TauCeti
