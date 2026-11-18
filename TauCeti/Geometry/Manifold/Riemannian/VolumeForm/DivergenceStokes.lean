/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence
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
the induced boundary volume form; the statement here keeps the flux-form side.

## Main results

* `TauCeti.integral_divergence_eq_integralTopForm_boundaryRestriction`: the divergence theorem
  `∫_M div X dV = ∫_{∂M} ι_X dV`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16,
  Theorem 16.32 (the divergence theorem).
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The flux form `ι_X dV` of a vector field `X` is supported in the topological support of `X`. -/
theorem tsupport_interior_riemannianVolumeForm_subset [IsManifold (𝓡∂ (n + 1)) 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) :
    _root_.tsupport (α := EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ)
        ((riemannianVolumeForm o).interior X) ⊆
      tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X := by
  refine closure_mono fun x hx ↦ Function.mem_support.2 fun h ↦ hx ?_
  ext v
  simp only [RoughForm.interior_apply, h]
  exact (riemannianVolumeForm o x).map_coord_zero 0 rfl

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
    (tsupport_interior_riemannianVolumeForm_subset o X)
  rw [← integralTopForm_mextDeriv o hφ hcφ,
    mextDeriv_interior_riemannianVolumeForm o (hX.mdifferentiable one_ne_zero),
    integralTopForm_smul_riemannianVolumeForm o
      (Manifold.contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
        (by simpa using hX)).continuous
      (hc.divergence _)]

end TauCeti
