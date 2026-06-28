/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Spatial pullbacks of semigroup-group positive-definite functions

This file records the spatial-coordinate pullback API for Berg--Christensen--Ressel
positive-definite functions on `ℝ≥0 × V`. If `F` is semigroup-group positive definite and
`φ : W →+ V` is an additive homomorphism, then `(t, w) ↦ F (t, φ w)` is again
semigroup-group positive definite.

This is a small prerequisite for the BCR semigroup--Bochner representation milestone in the
`OneParameterSemigroups` roadmap. The Bochner part is stated on an arbitrary finite-dimensional
real inner-product space, so downstream arguments need to transport the spatial variable along
additive equivalences and continuous linear maps without unfolding the private BCR wrapper.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
function API item "pullbacks" and Milestone 2 ("BCR semigroup--Bochner").

## Main declarations

* `TauCeti.IsSemigroupGroupPD.comp_spatialAddMonoidHom`: spatial pullback along an additive
  homomorphism.
* `TauCeti.IsSemigroupGroupPD.comp_spatialAddEquiv_iff`: invariance under a spatial additive
  equivalence.
* `TauCeti.IsSemigroupGroupPD.comp_spatialContinuousLinearMap`: the continuous-linear-map form
  used for real vector spaces.
* `TauCeti.IsSemigroupGroupPD.comp_spatialAddMonoidHom_and_continuous` and
  `TauCeti.IsSemigroupGroupPD.comp_spatialContinuousLinearMap_and_continuous`: packaged forms
  preserving both positive-definiteness and continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped NNReal

namespace TauCeti

namespace IsSemigroupGroupPD

variable {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  {F : ℝ≥0 × V → ℂ}

/-- Pulling back the spatial coordinate of a semigroup-group positive-definite function along an
additive homomorphism preserves semigroup-group positive-definiteness. -/
theorem comp_spatialAddMonoidHom (hF : IsSemigroupGroupPD F) (φ : W →+ V) :
    IsSemigroupGroupPD fun p : ℝ≥0 × W => F (p.1, φ p.2) := by
  refine IsSemigroupGroupPD.of_isPositiveDefiniteKernel ?_
  have hK := isPositiveDefiniteKernel_comp hF.isPositiveDefiniteKernel
    (fun p : ℝ≥0 × W => (p.1, φ p.2))
  simpa [map_sub] using hK

/-- Spatial pullbacks compose as expected. -/
theorem comp_spatialAddMonoidHom_comp (hF : IsSemigroupGroupPD F) (φ : W →+ V) (ψ : U →+ W) :
    IsSemigroupGroupPD fun p : ℝ≥0 × U => F (p.1, φ (ψ p.2)) :=
  (hF.comp_spatialAddMonoidHom φ).comp_spatialAddMonoidHom ψ

/-- Semigroup-group positive-definiteness is invariant under precomposition by a spatial
additive equivalence. -/
theorem comp_spatialAddEquiv_iff (e : W ≃+ V) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, e p.2)) ↔ IsSemigroupGroupPD F := by
  constructor
  · intro h
    have h' := h.comp_spatialAddMonoidHom e.symm.toAddMonoidHom
    simpa using h'
  · intro h
    exact h.comp_spatialAddMonoidHom e.toAddMonoidHom

section Topology

variable [TopologicalSpace V] [TopologicalSpace W]

/-- If the spatial additive homomorphism is continuous, spatial pullback preserves continuity. -/
theorem continuous_comp_spatialAddMonoidHom (hF : Continuous F) (φ : W →+ V)
    (hφ : Continuous φ) :
    Continuous fun p : ℝ≥0 × W => F (p.1, φ p.2) :=
  hF.comp (continuous_fst.prodMk (hφ.comp continuous_snd))

/-- Package spatial pullback of a semigroup-group positive-definite function with continuity
of the pulled-back function. -/
theorem comp_spatialAddMonoidHom_and_continuous (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (φ : W →+ V) (hφ : Continuous φ) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, φ p.2)) ∧
      Continuous (fun p : ℝ≥0 × W => F (p.1, φ p.2)) :=
  ⟨hFpd.comp_spatialAddMonoidHom φ, continuous_comp_spatialAddMonoidHom hFcont φ hφ⟩

end Topology

section ContinuousLinearMap

variable {E : Type*} {E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {G : ℝ≥0 × E → ℂ}

/-- Spatial pullback along a continuous linear map preserves semigroup-group
positive-definiteness. -/
theorem comp_spatialContinuousLinearMap (hG : IsSemigroupGroupPD G) (φ : E' →L[ℝ] E) :
    IsSemigroupGroupPD fun p : ℝ≥0 × E' => G (p.1, φ p.2) :=
  hG.comp_spatialAddMonoidHom φ.toAddMonoidHom

/-- Spatial pullback along a continuous linear equivalence is an equivalence on
semigroup-group positive-definiteness. -/
theorem comp_spatialContinuousLinearEquiv_iff (e : E' ≃L[ℝ] E) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × E' => G (p.1, e p.2)) ↔ IsSemigroupGroupPD G :=
  comp_spatialAddEquiv_iff e.toAddEquiv

/-- Package spatial pullback along a continuous linear map with preservation of continuity. -/
theorem comp_spatialContinuousLinearMap_and_continuous (hGpd : IsSemigroupGroupPD G)
    (hGcont : Continuous G) (φ : E' →L[ℝ] E) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × E' => G (p.1, φ p.2)) ∧
      Continuous (fun p : ℝ≥0 × E' => G (p.1, φ p.2)) :=
  hGpd.comp_spatialAddMonoidHom_and_continuous hGcont φ.toAddMonoidHom φ.continuous

end ContinuousLinearMap

end IsSemigroupGroupPD

end TauCeti
