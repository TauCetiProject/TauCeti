/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# Equal-rank spectral projector perturbation

An interval/exterior point-spectrum gap bounds the directed sine map by the
operator perturbation. For two invariant subspaces of equal finite dimension,
the directed sine norm equals the norm of the difference of their orthogonal
projections. We combine these results to obtain the canonical spectral-projector
Davis--Kahan bound with constant one.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1--46.
* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
* The corresponding spectral-subspace and perturbation results in the
  AIQ-Kitware DKPS formalization (Apache-2.0).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- For invariant subspaces of equal dimension, an interval/exterior spectral
gap turns the directed Davis--Kahan bound into a bound on the full projector
difference. -/
theorem mul_projectionGap_le_norm_sub_of_pointIntervalExteriorGap
    {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    (hrank : Module.finrank 𝕜 U = Module.finrank 𝕜 V) {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * U.projectionGap V ≤ ‖B - A‖ := by
  have hround (T : E →L[𝕜] E) :
      LinearMap.toContinuousLinearMap (T : E →ₗ[𝕜] E) = T := by
    exact ContinuousLinearMap.coe_injective rfl
  have hsin : δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ ‖B - A‖ := by
    simpa only [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
      map_sub, hround] using
      (TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub
        (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 E E)
        (A := A) (B := B) (U := U) (V := V) hA hB hU hV hgap)
  calc
    δ * U.projectionGap V = δ * U.directedProjectionGap V := by
      rw [Submodule.projectionGap_eq_directedProjectionGap_of_finrank_eq U V hrank]
    _ = δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
      rw [Submodule.directedProjectionGap_def]
    _ ≤ ‖B - A‖ := hsin

end Submodule

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The equal-rank spectral-projector Davis--Kahan theorem.
For equally ranked point-spectral subspaces of self-adjoint operators, an
interval/exterior gap gives `δ * ‖P_A - P_B‖ ≤ ‖B - A‖`. The selected spectra
need not be contiguous; the separation is expressed on the restricted point
spectra of the selected blocks. -/
theorem mul_norm_sub_starProjection_pointSpectralSubspace_le
    (A B : E →L[𝕜] E)
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {s t : Set ℝ} {a b δ : ℝ}
    (hrank : Module.finrank 𝕜 (Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) s) =
      Module.finrank 𝕜 (Module.End.pointSpectralSubspace (B : E →ₗ[𝕜] E) t))
    (hgap : PointIntervalExteriorGap (A : E →ₗ[𝕜] E)
      (Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) s) (B : E →ₗ[𝕜] E)
      (Module.End.pointSpectralSubspace (B : E →ₗ[𝕜] E) t)ᗮ a b δ) :
    δ * ‖(Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) s).starProjection -
      (Module.End.pointSpectralSubspace (B : E →ₗ[𝕜] E) t).starProjection‖ ≤ ‖B - A‖ := by
  let U : Submodule 𝕜 E := Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) s
  let V : Submodule 𝕜 E := Module.End.pointSpectralSubspace (B : E →ₗ[𝕜] E) t
  have hU : ∀ x ∈ U, A x ∈ U := by
    intro x hx
    exact (Module.End.map_pointSpectralSubspace_le
      (A := (A : E →ₗ[𝕜] E)) (Ω := s)) (Submodule.mem_map_of_mem hx)
  have hV : ∀ x ∈ V, B x ∈ V := by
    intro x hx
    exact (Module.End.map_pointSpectralSubspace_le
      (A := (B : E →ₗ[𝕜] E)) (Ω := t)) (Submodule.mem_map_of_mem hx)
  have h := Submodule.mul_projectionGap_le_norm_sub_of_pointIntervalExteriorGap
    (A := A) (B := B) (U := U) (V := V) hA hB hU hV hrank hgap
  simpa only [Submodule.projectionGap_def, U, V] using h

end Module.End
