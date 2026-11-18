/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Degree and Riemannian volume

For a smooth map between compact oriented manifolds of equal dimension, integrating the
pullback of the target's Riemannian volume form gives the degree times the target volume.
This is the area-counting step for conformal maps of closed surfaces, including branched maps.

## References

* The degree–volume formulas were ported from Riccardo Brasca's `ForTauCeti` formalization.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 17.35.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [BoundarylessManifold J N] [T2Space N] [ConnectedSpace N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ E (fun y : N ↦ TangentSpace J y)]
  {k : ℕ}

/-- The Riemannian area formula for a smooth map of compact oriented manifolds of equal
dimension. Branch points need no special treatment: the degree formula integrates the actual
pullback top form over the whole source. -/
theorem integralTopForm_mpullback_riemannianVolumeForm_eq_degree_mul_volume
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k))
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    integralTopForm o (mpullback I J f (riemannianVolumeForm o')) =
      degree o o' f * riemannianTotalVolume J N := by
  have : IsManifold J ((∞ : WithTop ℕ∞) + 1) N := by simpa using (inferInstance :
    IsManifold J ∞ N)
  rw [integralTopForm_mpullback_eq_degree_mul o o' hf hf.continuous.isProperMap
    (isSmoothForm_riemannianVolumeForm o')
    (isClosed_tsupport _).isCompact, integralTopForm_riemannianVolumeForm]

variable [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- If the pullback of the target volume form has Jacobian `j`, its Riemannian integral is
the degree times the target volume. The equality of forms is pointwise and remains meaningful
at branch points, where the Jacobian vanishes. -/
theorem integral_jacobian_eq_degree_mul_volume
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k))
    {f : M → N} (hf : ContMDiff I J ∞ f) {j : M → ℝ} (hj : Continuous j)
    (hform : mpullback I J f (riemannianVolumeForm o') =
      fun x ↦ j x • riemannianVolumeForm o x) :
    (∫ x, j x ∂riemannianVolume I M) =
      degree o o' f * riemannianTotalVolume J N := by
  rw [← integralTopForm_smul_riemannianVolumeForm o hj
    (HasCompactSupport.of_compactSpace _), ← hform]
  exact integralTopForm_mpullback_riemannianVolumeForm_eq_degree_mul_volume o o' hf

end TauCeti
