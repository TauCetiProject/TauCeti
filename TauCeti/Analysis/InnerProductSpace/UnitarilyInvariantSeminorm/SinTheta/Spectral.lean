/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# Canonical spectral-subspace residual sine bounds

The residual Davis--Kahan theorem applies to arbitrary invariant subspaces of a symmetric
operator. A point-spectral subspace is canonically invariant, and its orthogonal complement
is the point-spectral subspace for the complementary spectral set. Thus the residual theorem
can be stated directly in terms of spectral selection, without a separate invariance hypothesis.

The first theorem permits any spectral selection with the appropriate exterior spectral
condition. The second specializes to the canonical selection by the enlarged interval:
there the exterior spectral condition is automatic.

## Source

The residual bound and point-spectral-subspace construction have antecedents in the
maintained AIQ-Kitware DKPS formalization:
https://github.com/AIQ-Kitware/aiq-dkps-formalization

* `ForTauCeti/Analysis/InnerProductSpace/SinTheta/DirectedBounds.lean`
  (the residual `sin Θ` theorem).
* `ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean`
  (point-spectral subspaces and their invariance).

Original source copyright: Copyright (c) 2026 Kitware, Inc. All rights reserved.
The source files are released under Apache-2.0.

## References

* C. Davis, W. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169,
  Springer (1997), §VII.3.
-/

public section

open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {a b δ : ℝ}

/-- **Canonical spectral-subspace residual Davis--Kahan bound.**

The spectral selection `Ω` identifies the target subspace of the symmetric operator `A`.
Its complementary point-spectral subspace carries spectrum outside the enlarged interval,
while the trial-coordinate operator `M` carries spectrum inside `[a,b]`. The residual controls
the directed sine in every rectangular unitarily invariant seminorm. -/
theorem mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →L[𝕜] E} {M : F →L[𝕜] F}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hM : (M : F →ₗ[𝕜] F).IsSymmetric)
    (Ω : Set ℝ)
    (hMspec : Module.End.PointSpectrumIn (M : F →ₗ[𝕜] F) ⊤ (Set.Icc a b))
    (hAspec : Module.End.PointSpectrumIn (A : E →ₗ[𝕜] E)
      (Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) Ωᶜ)
      (Set.Ioo (a - δ) (b + δ))ᶜ)
    (X : F →L[𝕜] E) :
    δ * N ((Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) Ω)ᗮ.starProjection ∘L X) ≤
      N (A.sylvester M X) := by
  let U : Submodule 𝕜 E := Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E) Ω
  have hU : ∀ x ∈ U, A x ∈ U := by
    intro x hx
    exact (Module.End.map_pointSpectralSubspace_le
      (A := (A : E →ₗ[𝕜] E)) (Ω := Ω)) (Submodule.mem_map_of_mem hx)
  have hAspec' : Module.End.PointSpectrumIn (A : E →ₗ[𝕜] E) Uᗮ
      (Set.Ioo (a - δ) (b + δ))ᶜ := by
    rw [hA.orthogonal_pointSpectralSubspace Ω]
    exact hAspec
  have hgap : Module.End.PointIntervalExteriorGap (M : F →ₗ[𝕜] F) ⊤
      (A : E →ₗ[𝕜] E) Uᗮ a b δ := ⟨hMspec, hAspec'⟩
  exact N.mul_map_starProjection_comp_le_map_sylvester_apply hA hM hU hgap X

/-- The canonical interval spectral selection needs no explicit exterior spectral assumption:
its orthogonal complement is selected by the exterior of the enlarged interval. -/
theorem mul_map_starProjection_orthogonal_pointSpectralSubspace_Ioo_comp_le_map_sylvester_apply
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →L[𝕜] E} {M : F →L[𝕜] F}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hM : (M : F →ₗ[𝕜] F).IsSymmetric)
    (hMspec : Module.End.PointSpectrumIn (M : F →ₗ[𝕜] F) ⊤ (Set.Icc a b))
    (X : F →L[𝕜] E) :
    δ * N ((Module.End.pointSpectralSubspace (A : E →ₗ[𝕜] E)
        (Set.Ioo (a - δ) (b + δ)))ᗮ.starProjection ∘L X) ≤ N (A.sylvester M X) := by
  exact N.mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply
    hA hM (Set.Ioo (a - δ) (b + δ)) hMspec
    (Module.End.pointSpectrumIn_pointSpectralSubspace
      (A : E →ₗ[𝕜] E) (Set.Ioo (a - δ) (b + δ))ᶜ) X

end TauCeti.UnitarilyInvariantSeminorm
