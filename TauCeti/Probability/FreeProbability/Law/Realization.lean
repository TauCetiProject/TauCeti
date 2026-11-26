/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
import TauCeti.Analysis.RCLike.ContinuousMap
import TauCeti.Probability.FreeProbability.FreeProduct.Reduced

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
open scoped ComplexOrder InnerProductSpace

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

section Realization

variable {I : Type u} (K : I → Set ℝ) [∀ i, CompactSpace (K i)] (μ : I → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)]

/-- Integration against `μ i` on `C(K i, ℂ)`. -/
private def factorState (i : I) : StarPositiveFunctional C(K i, ℂ) :=
  .ofPositiveLinearMap (ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : K i → ℝ)))

private theorem factorState_apply (i : I) (g : C(K i, ℂ)) :
    factorState K μ i g = ContinuousMap.integralPositiveLinearMap ((μ i).comap (↑)) g :=
  StarPositiveFunctional.ofPositiveLinearMap_apply _ g

private theorem factorState_one (hK : ∀ i, μ i (K i)ᶜ = 0) (i : I) :
    factorState K μ i 1 = 1 :=
  (factorState_apply K μ i 1).trans
    (ContinuousMap.integralPositiveLinearMap_comap_subtypeVal_one (hK i))

/-- The coordinate function `x ↦ x` on `K i`. -/
private def coord (i : I) : C(K i, ℂ) :=
  (ContinuousMap.restrict (K i) (ContinuousMap.id ℝ)).realToRCLike ℂ

omit [∀ i, CompactSpace (K i)] in
private theorem isSelfAdjoint_coord (i : I) : IsSelfAdjoint (coord K i) :=
  ContinuousMap.isSelfAdjoint_realToRCLike ℂ

/-- Star homomorphisms `f i : C(K i, ℂ) → B(H)` with free ranges for the vector state at a unit
vector `ξ`, along which this vector state restricts to integration against `μ i`, realize the
`μ i` by the images of the coordinate functions. Stated for an arbitrary Hilbert space so that
the C⋆-algebra, order and ring instances on its bounded operators are inferred uniformly. -/
private theorem exists_realization_of_starAlgHom {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ξ : H) (hξ : ‖ξ‖ = 1)
    (f : ∀ i, C(K i, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hfree : IsFreelyIndependent (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap
      fun i => (f i).toAlgHom.range)
    (hf : ∀ i g, ⟪ξ, f i g ξ⟫_ℂ = factorState K μ i g) (hK : ∀ i, μ i (K i)ᶜ = 0) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : I → A), φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ (∀ i, law φ (a i) = μ i) ∧
          ∀ i, spectrum ℝ (a i) ⊆ K i := by
  have ha (i : I) : IsSelfAdjoint (f i (coord K i)) := (isSelfAdjoint_coord K i).map (f i)
  refine ⟨H →L[ℂ] H, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.innerPositiveLinearMap ℂ ξ, fun i => f i (coord K i), by simp [hξ], ha,
    hfree.isFreelyIndependentElements_of_mem fun i => AlgHom.mem_range_self _ (coord K i),
    fun i => ?_, fun i => ?_⟩
  · refine ((eq_law_iff_forall_integral_pow (ha i) (isCompact_iff_compactSpace.2 inferInstance)
      (hK i)).2 fun n => ?_).symm
    rw [← law_integralPositiveLinearMap_comap_restrict_id (hK i),
      ofReal_integral_pow_law _ (ContinuousMap.isSelfAdjoint_realToRCLike ℂ), ← map_pow,
      ContinuousLinearMap.innerPositiveLinearMap_apply, hf, factorState_apply, coord]
  · have hs : spectrum ℝ (coord K i) = K i :=
      ContinuousMap.spectrum_realToRCLike_restrict_id ℂ (K i)
    rw [← hs, ← spectrum.preimage_algebraMap ℂ,
      ← spectrum.preimage_algebraMap ℂ (a := coord K i)]
    exact Set.preimage_mono (AlgHom.spectrum_apply_subset (f i) (coord K i))

/-- Realization of the `μ i`, concentrated on the compact sets `K i`, by free coordinate
functions in the reduced free product of the `C(K i, ℂ)`. -/
private theorem exists_realization (hK : ∀ i, μ i (K i)ᶜ = 0) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : I → A), φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ (∀ i, law φ (a i) = μ i) ∧
          ∀ i, spectrum ℝ (a i) ⊆ K i := by
  classical
  let ψ := factorState K μ
  have hψ := factorState_one K μ hK
  let ξ := ReducedFreeProduct.vacuum ψ hψ
  let π := ReducedFreeProduct.representation ψ hψ
  let ι := LinearAlgebra.FreeProduct.ι ℂ (fun i => C(K i, ℂ))
  have hω (x : LinearAlgebra.FreeProduct ℂ fun i => C(K i, ℂ)) :
      ⟪ξ, π x ξ⟫_ℂ = freeProductPositiveFunctional ψ hψ x := by
    rw [← ReducedFreeProduct.state_ofAlgebraic, ReducedFreeProduct.state_apply,
      ReducedFreeProduct.coe_ofAlgebraic]
  have hfree := (isFreelyIndependent_freeProductExpectation (fun i => (ψ i).toLinearMap) hψ).map
    π.toAlgHom (φ' := (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap)
    (LinearMap.ext fun x => (ContinuousLinearMap.innerPositiveLinearMap_apply ξ (π x)).trans
      ((hω x).trans (freeProductPositiveFunctional_apply ψ hψ x)))
  refine exists_realization_of_starAlgHom K μ ξ (ReducedFreeProduct.norm_vacuum ψ hψ)
    (fun i => π.comp (LinearAlgebra.FreeProduct.ιStar ℂ (fun i => C(K i, ℂ)) i)) ?_
    (fun i g => ?_) hK
  · have hrange (i : I) :
        (π.comp (LinearAlgebra.FreeProduct.ιStar ℂ (fun i => C(K i, ℂ)) i)).toAlgHom.range =
          (ι i).range.map π.toAlgHom := by
      rw [← AlgHom.range_comp]
      congr 1
      ext x
      simp [ι, LinearAlgebra.FreeProduct.ιStar_apply]
    simpa only [hrange] using hfree
  · rw [StarAlgHom.comp_apply, LinearAlgebra.FreeProduct.ιStar_apply, hω,
      freeProductPositiveFunctional_ι]

end Realization

/-- **Free realization of compactly supported laws.** Every family `(μ i)` of compactly
supported probability measures on `ℝ` is the family of laws of freely independent selfadjoint
elements `a i` of a C⋆-algebra with a state `φ`, with the spectrum of each `a i` contained in the
support of `μ i`. -/
theorem exists_isFreelyIndependentElements_law_eq {I : Type u} (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : I → A), φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ (∀ i, law φ (a i) = μ i) ∧
          ∀ i, spectrum ℝ (a i) ⊆ (μ i).support :=
  have := fun i => isCompact_iff_compactSpace.1 (hμ i)
  exists_realization (fun i => (μ i).support) μ fun _ => Measure.measure_compl_support

end TauCeti
