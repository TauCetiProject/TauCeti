/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.ExteriorSquare
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.TwoForm

/-!
# Naturality of the two-form curvature operator

Pullback by the differential of a local Riemannian isometry intertwines the curvature
endomorphisms on real two-forms. This uses the existing musical identification and the
naturality of the bivector curvature endomorphism, so the statement holds on all two-forms,
including those that are not decomposable. No global injectivity or surjectivity is needed.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7–8.
* `TauCeti.IsLocalRiemannianIsometry.map_curvatureEndomorphism`.
-/

public section

open Bundle Manifold CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

/-- The curvature endomorphism on real two-forms commutes with pullback by a local
Riemannian isometry, including in individual sheets of a Riemannian covering. -/
@[simp]
theorem curvatureFormEndomorphism_comp_mfderiv (hf : IsLocalRiemannianIsometry I J f)
    (x : M) (β : TangentSpace J (f x) [⋀^Fin 2]→L[ℝ] ℝ) :
    (leviCivitaConnection I M).curvatureFormEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x
        (β.compContinuousLinearMap (mfderiv I J f x)) =
      ((leviCivitaConnection J N).curvatureFormEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x) β).compContinuousLinearMap
          (mfderiv I J f x) := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  have heL : e.toLinearEquiv.toLinearMap = (mfderiv I J f x).toLinearMap := LinearMap.ext he
  have heI : e.toLinearIsometry.toLinearMap = (mfderiv I J f x).toLinearMap :=
    LinearMap.ext he
  have heC : e.toLinearIsometry.toContinuousLinearMap = mfderiv I J f x :=
    ContinuousLinearMap.ext he
  have hmus (a : ⋀[ℝ]^2 (TangentSpace I x)) :
      (alternatingFormEquiv (TangentSpace J (f x)) 2
        (exteriorPower.map 2 (mfderiv I J f x).toLinearMap a)).compContinuousLinearMap
          (mfderiv I J f x) =
        alternatingFormEquiv (TangentSpace I x) 2 a := by
    rw [← heI, ← heC]
    exact e.toLinearIsometry.alternatingFormEquiv_map a
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv (TangentSpace J (f x)) 2).surjective β
  have hs : Function.Surjective (exteriorPower.map 2 (mfderiv I J f x).toLinearMap) := by
    rw [← heL]
    exact (e.toLinearEquiv.exteriorPower 2).surjective
  obtain ⟨a, rfl⟩ := hs a
  rw [hmus, curvatureFormEndomorphism_alternatingFormEquiv,
    curvatureFormEndomorphism_alternatingFormEquiv, ← hf.map_curvatureEndomorphism, hmus]

end TauCeti.IsLocalRiemannianIsometry
