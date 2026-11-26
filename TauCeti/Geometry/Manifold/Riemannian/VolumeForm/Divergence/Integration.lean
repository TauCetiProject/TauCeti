/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Volume
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.Geometry.Manifold.Riemannian.Boundary.Flux

/-!
# Integral comparisons for the Riemannian volume form and divergence

This module compares top-form integrals involving the Riemannian volume form `dV` and its interior
product `ι_X dV` with measure integrals against the Riemannian volume and boundary volume:

* `TauCeti.integralTopForm_mextDeriv_interior_riemannianVolumeForm`:
  `∫_M d(ι_X dV) = ∫_M div X dV` on any oriented `C²` Riemannian manifold (with or without
  boundary).
* `TauCeti.integralTopForm_boundaryRestriction_interior_riemannianVolumeForm`:
  `∫_{∂M} ι^*(ι_X dV) = ∫_{∂M} ⟪X, N⟫ dS` on an oriented `C¹` half-space Riemannian manifold with
  boundary and continuous metric.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16,
  Theorem 16.32 (the divergence theorem).
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

/-- On any oriented `C²` Riemannian manifold (with or without boundary),
`∫_M d(ι_X dV) = ∫_M div X dV` for any compactly supported `C¹` vector field `X`. -/
theorem integralTopForm_mextDeriv_interior_riemannianVolumeForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {m : ℕ} (o : Manifold.Orientation I M (Fin (m + 1)))
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hc : HasCompactSupport (β := E) X) :
    integralTopForm o (mextDeriv ((riemannianVolumeForm o).interior X)) =
      ∫ x, Manifold.divergence I X x ∂riemannianVolume I M := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  rw [mextDeriv_interior_riemannianVolumeForm o (hX.mdifferentiable one_ne_zero)]
  exact integralTopForm_smul_riemannianVolumeForm o
    (Manifold.continuous_divergence (by simpa using hX)) (hc.divergence I)

/-- On an oriented `C¹` half-space Riemannian manifold with boundary and continuous metric, the
boundary top-form integral of `ι^*(ι_X dV)` equals `∫_{∂M} ⟪X, N⟫ dS` for any compactly supported
continuous vector field `X`. -/
theorem integralTopForm_boundaryRestriction_interior_riemannianVolumeForm
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) 1 M] [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hX : Continuous (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    integralTopForm (boundaryOrientation o)
        (boundaryRestriction ((riemannianVolumeForm o).interior X)) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M
  rw [funext (boundaryRestriction_interior_riemannianVolumeForm o X),
    halfSpaceBoundaryVolume_eq_riemannianVolume]
  exact integralTopForm_smul_riemannianVolumeForm (boundaryOrientation o)
    (continuous_boundaryFlux hX) (hasCompactSupport_boundaryFlux hc)

end TauCeti
