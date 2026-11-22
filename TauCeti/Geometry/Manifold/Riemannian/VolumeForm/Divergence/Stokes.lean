/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# The divergence theorem on an oriented manifold with boundary

Let `M` be an oriented smooth manifold with boundary carrying a `C¹` Riemannian metric, with
Riemannian volume form `dV`. For a compactly supported `C¹` vector field `X`, the integral of the
divergence of `X` against the Riemannian volume is the integral over the boundary, with its
outward-first orientation, of the restriction of the flux form `ι_X dV`:

`∫_M div X dV = ∫_{∂M} ι_X dV`.

This is Stokes' theorem for `ι_X dV`, combined with the identity `d (ι_X dV) = (div X) dV` and the
identification of the integral of `f dV` with the integral of `f` against the Riemannian measure.
On the boundary, `ι_X dV` restricts to `⟨X, N⟩ dA`, where `N` is the outward unit normal and `dA`
the induced boundary volume form; the statement here keeps the flux-form side and compares both
sides with the orientation-free divergence theorem.

## Main results

* `TauCeti.integralTopForm_mextDeriv_interior_riemannianVolumeForm`: identifies the top-form
  integrals of `d(ι_X dV)` and `ι^*(ι_X dV)` with `∫ div X dV` and `∫_{∂M} ⟪X, N⟫ dS`.
* `TauCeti.integral_divergence_eq_integralTopForm_boundaryRestriction`: the divergence theorem
  `∫_M div X dV = ∫_{∂M} ι_X dV`.

This module is ported from Riccardo Brasca’s ForTauCeti formalization of the divergence theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16,
  Theorem 16.32 (the divergence theorem).
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

section Comparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 2 M] [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance instIsManifoldOneStokesComparison : IsManifold (𝓡∂ (n + 1)) 1 M :=
  IsManifold.of_le (n := 2) (by norm_num)
local instance instIsManifoldBoundaryStokesComparison :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

/-- **Comparison of Stokes' theorem for `ι_X dV` with the Riemannian divergence theorem.** On an
oriented `C²` Riemannian manifold with boundary, the top-form integral of `d(ι_X dV)` equals
`∫ div X dV` and the boundary top-form integral of `ι^*(ι_X dV)` equals `∫_{∂M} ⟪X, N⟫ dS`,
identifying the two sides of Stokes' theorem with the two sides of the divergence theorem. -/
theorem integralTopForm_mextDeriv_interior_riemannianVolumeForm
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    integralTopForm o (mextDeriv ((riemannianVolumeForm o).interior X)) =
        (∫ x, Manifold.divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) ∧
      integralTopForm (boundaryOrientation o)
          (boundaryRestriction ((riemannianVolumeForm o).interior X)) =
        ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by norm_num; infer_instance
  refine ⟨?_, ?_⟩
  · rw [mextDeriv_interior_riemannianVolumeForm o (hX.mdifferentiable one_ne_zero)]
    exact integralTopForm_smul_riemannianVolumeForm o
      (Manifold.contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
        (by simpa using hX)).continuous (hc.divergence (𝓡∂ (n + 1)))
  · rw [funext (boundaryRestriction_interior_riemannianVolumeForm o X),
      halfSpaceBoundaryVolume_eq_riemannianVolume]
    exact integralTopForm_smul_riemannianVolumeForm (boundaryOrientation o)
      (continuous_boundaryFlux hX.continuous) (hasCompactSupport_boundaryFlux hc)

end Comparison

section Stokes

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

variable [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- **The divergence theorem** on an oriented manifold with boundary: for a compactly supported
`C¹` vector field `X`, the integral of `div X` against the Riemannian volume is the integral of the
flux form `ι_X dV` over the boundary, with its outward-first orientation. -/
theorem integral_divergence_eq_integralTopForm_boundaryRestriction
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    ∫ x, Manifold.divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M =
      integralTopForm (boundaryOrientation o)
        (boundaryRestriction ((riemannianVolumeForm o).interior X)) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by norm_num; infer_instance
  have hφ := (isSmoothForm_riemannianVolumeForm (n := 1) o).interior hX
  have hcφ := hc.of_isClosed_subset (isClosed_tsupport _)
    ((riemannianVolumeForm o).tsupport_interior_subset X)
  rw [← integralTopForm_mextDeriv o hφ hcφ,
    mextDeriv_interior_riemannianVolumeForm o (hX.mdifferentiable one_ne_zero),
    integralTopForm_smul_riemannianVolumeForm o
      (Manifold.contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
        (by simpa using hX)).continuous
      (hc.divergence _)]

end Stokes

end TauCeti
