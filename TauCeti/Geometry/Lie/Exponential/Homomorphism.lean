/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.LocalInverse
import TauCeti.Geometry.Manifold.Algebra.Monoid

/-!
# Recognizing smooth homomorphisms through the exponential

A group homomorphism between finite-dimensional real Lie groups is smooth if it intertwines
exponential maps through a linear map of their Lie algebras. No continuity or connectedness
assumption is needed. This criterion recognizes homomorphisms between intrinsic immersed
subgroup presentations from the linear maps between their Lie algebras.

## Main results

* `TauCeti.Lie.contMDiff_of_map_lieExp`: exponential intertwining implies smoothness.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Proposition 20.8(a, f),
  pp.519–521, for smoothness of the exponential and its local smooth inverse.
-/

public section

noncomputable section

open Filter Function Manifold
open scoped ContDiff Manifold Topology

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

/-- A group homomorphism intertwining the exponential maps through a linear map of Lie
algebras is smooth. Continuity of the homomorphism is not required. -/
theorem contMDiff_of_map_lieExp {F : Type*} [FunLike F G G'] [MonoidHomClass F G G']
    (f : F) (L : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (h : let _ : T2Space G := I.t2Space_of_lieGroup ∞
      let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
      ∀ X, f (lieExp X) = lieExp (L X)) : ContMDiff I I' ∞ f := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  let A := LinearMap.toContinuousLinearMap L
  have hev : (fun g ↦ lieExp (A (lieLog (I := I) g))) =ᶠ[𝓝 1] f := by
    filter_upwards [eventually_lieExp_lieLog (I := I) (G := G)] with g hg
    exact (h (lieLog (I := I) g)).symm.trans (congrArg f hg)
  have hsmooth : ContMDiffAt I I' ∞ (fun g ↦ lieExp (A (lieLog (I := I) g))) 1 :=
    (contMDiff_lieExp (I := I') (G := G')).contMDiffAt.comp 1
      (A.contDiff.contMDiff.contMDiffAt.comp 1 (contMDiffAt_lieLog_one (I := I) (G := G)))
  exact contMDiff_of_contMDiffAt_mulHom f (hsmooth.congr_of_eventuallyEq hev.symm)

end TauCeti.Lie
