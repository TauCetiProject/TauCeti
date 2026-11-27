/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence.Integration

/-!
# The divergence theorem on an oriented manifold with boundary

Let `M` be an oriented smooth manifold with boundary carrying a `C¹` Riemannian metric, with
Riemannian volume form `dV`. For a compactly supported `C¹` vector field `X`, the integral of the
divergence of `X` against the Riemannian volume is the integral over the boundary, with its
outward-first orientation, of the restriction of the flux form `ι_X dV`:

`∫_M div X dV = ∫_{∂M} ι_X dV`.

This is Stokes' theorem for `ι_X dV`, combined with the identity `d (ι_X dV) = (div X) dV` and the
identification of the integral of `f dV` with the integral of `f` against the Riemannian measure
(`TauCeti.integralTopForm_mextDeriv_interior_riemannianVolumeForm`).

## Main results

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
  have : IsManifold (𝓡∂ (n + 1)) 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hφ := (isSmoothForm_riemannianVolumeForm (n := 1) o).interior hX
  have hcφ := hc.of_isClosed_subset (isClosed_tsupport _)
    ((riemannianVolumeForm o).tsupport_interior_subset X)
  rw [← integralTopForm_mextDeriv o hφ hcφ,
    integralTopForm_mextDeriv_interior_riemannianVolumeForm o hX hc]

end Stokes

end TauCeti
