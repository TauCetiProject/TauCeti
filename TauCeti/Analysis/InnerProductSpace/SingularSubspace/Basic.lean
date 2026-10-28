/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Left and right singular subspaces

A linear map `A : E →ₗ[𝕜] F` between finite-dimensional real or complex inner product
spaces has two positive Gram operators: `A† ∘ₗ A` on `E` and `A ∘ₗ A†` on `F`.
Their point-spectral subspaces, selected by a set of **squared** singular values
`Ω ⊆ ℝ`, are the right and left singular subspaces of `A`.

The definitions reuse `Module.End.pointSpectralSubspace`, rather than creating a
second spectral-subspace construction or naming duplicate Gram operators.
Consequently the general point-spectrum API supplies monotonicity, operator
invariance, and restricted-spectrum containment.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
* Adapted from the AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
  at `YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The right singular subspace of `A`, selected by the squared singular
values in `Ω`, is the point-spectral subspace of `A† A` on its source. -/
noncomputable def rightSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  Module.End.pointSpectralSubspace (A.adjoint ∘ₗ A) Ω

/-- The left singular subspace of `A`, selected by the squared singular
values in `Ω`, is the point-spectral subspace of `A A†` on its target. -/
noncomputable def leftSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 F :=
  Module.End.pointSpectralSubspace (A ∘ₗ A.adjoint) Ω

/-- The defining point-spectral-subspace formula for the right singular block. -/
theorem rightSingularSubspace_eq_pointSpectralSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    A.rightSingularSubspace Ω =
      Module.End.pointSpectralSubspace (A.adjoint ∘ₗ A) Ω :=
  (rfl)

/-- The defining point-spectral-subspace formula for the left singular block. -/
theorem leftSingularSubspace_eq_pointSpectralSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    A.leftSingularSubspace Ω =
      Module.End.pointSpectralSubspace (A ∘ₗ A.adjoint) Ω :=
  (rfl)

/-- The right singular subspace of the adjoint is the left singular subspace
of the original map. -/
@[simp]
theorem rightSingularSubspace_adjoint (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    A.adjoint.rightSingularSubspace Ω = A.leftSingularSubspace Ω := by
  rw [rightSingularSubspace_eq_pointSpectralSubspace, adjoint_adjoint,
    leftSingularSubspace_eq_pointSpectralSubspace]

/-- The left singular subspace of the adjoint is the right singular subspace
of the original map. -/
@[simp]
theorem leftSingularSubspace_adjoint (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    A.adjoint.leftSingularSubspace Ω = A.rightSingularSubspace Ω := by
  rw [leftSingularSubspace_eq_pointSpectralSubspace, adjoint_adjoint,
    rightSingularSubspace_eq_pointSpectralSubspace]

/-- Enlarging the selected squared singular values enlarges the right block. -/
theorem rightSingularSubspace_mono (A : E →ₗ[𝕜] F) {Ω Ω' : Set ℝ}
    (hΩ : Ω ⊆ Ω') : A.rightSingularSubspace Ω ≤ A.rightSingularSubspace Ω' := by
  simpa only [rightSingularSubspace_eq_pointSpectralSubspace] using
    (Module.End.pointSpectralSubspace_mono (A := A.adjoint ∘ₗ A) hΩ)

/-- Enlarging the selected squared singular values enlarges the left block. -/
theorem leftSingularSubspace_mono (A : E →ₗ[𝕜] F) {Ω Ω' : Set ℝ}
    (hΩ : Ω ⊆ Ω') : A.leftSingularSubspace Ω ≤ A.leftSingularSubspace Ω' := by
  simpa only [leftSingularSubspace_eq_pointSpectralSubspace] using
    (Module.End.pointSpectralSubspace_mono (A := A ∘ₗ A.adjoint) hΩ)

/-- The right singular block is invariant under the right Gram operator. -/
theorem map_rightSingularSubspace_le (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule.map (A.adjoint ∘ₗ A) (A.rightSingularSubspace Ω) ≤
      A.rightSingularSubspace Ω := by
  simpa only [rightSingularSubspace_eq_pointSpectralSubspace] using
    (Module.End.map_pointSpectralSubspace_le (A := A.adjoint ∘ₗ A) (Ω := Ω))

/-- The left singular block is invariant under the left Gram operator. -/
theorem map_leftSingularSubspace_le (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule.map (A ∘ₗ A.adjoint) (A.leftSingularSubspace Ω) ≤
      A.leftSingularSubspace Ω := by
  simpa only [leftSingularSubspace_eq_pointSpectralSubspace] using
    (Module.End.map_pointSpectralSubspace_le (A := A ∘ₗ A.adjoint) (Ω := Ω))

/-- All real eigenvalues carried by the right singular block lie in `Ω`. -/
theorem pointSpectrumIn_rightSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Module.End.PointSpectrumIn (A.adjoint ∘ₗ A) (A.rightSingularSubspace Ω) Ω := by
  simpa only [rightSingularSubspace_eq_pointSpectralSubspace] using
    Module.End.pointSpectrumIn_pointSpectralSubspace (A.adjoint ∘ₗ A) Ω

/-- All real eigenvalues carried by the left singular block lie in `Ω`. -/
theorem pointSpectrumIn_leftSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Module.End.PointSpectrumIn (A ∘ₗ A.adjoint) (A.leftSingularSubspace Ω) Ω := by
  simpa only [leftSingularSubspace_eq_pointSpectralSubspace] using
    Module.End.pointSpectrumIn_pointSpectralSubspace (A ∘ₗ A.adjoint) Ω

end LinearMap
