/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Two-vector quadratic-form identities in real or complex inner-product spaces

Three elementary lemmas useful for block-operator perturbation estimates:

* `LinearMap.IsSymmetric.re_inner_map_symm`: the real mixed coefficients agree for symmetric maps;
* `LinearMap.re_inner_smul_add_smul_map`: expand the real quadratic form of a two-vector
  real-linear combination;
* `TauCeti.norm_smul_add_smul_sq`: the Pythagorean norm formula for a two-vector
  real-linear combination when the real part of the mixed inner product vanishes.

No finite-dimensionality, spectral-gap, or eigenvector assumptions are needed. The results
are used by the per-eigenvector double-angle estimates in `DoubleAngle.Vector`.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {H : E →ₗ[𝕜] E}

namespace LinearMap.IsSymmetric

/-- Real parts of the two mixed entries of a symmetric operator agree; the
reason no complex phase alignment is needed anywhere in this file. -/
theorem re_inner_map_symm (hH : H.IsSymmetric) (y z : E) :
    RCLike.re ⟪z, H y⟫_𝕜 = RCLike.re ⟪y, H z⟫_𝕜 := by
  rw [← hH z y, inner_re_symm]

end LinearMap.IsSymmetric

namespace LinearMap

/-- Quadratic form of an operator at a real linear combination of two vectors,
expanded into the four scalar entries.  Pure sesquilinear algebra. -/
theorem re_inner_smul_add_smul_map (H : E →ₗ[𝕜] E) (y z : E) (γ σ : ℝ) :
    RCLike.re ⟪(γ : 𝕜) • y + (σ : 𝕜) • z, H ((γ : 𝕜) • y + (σ : 𝕜) • z)⟫_𝕜
      = γ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 + σ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
        + γ * σ * (RCLike.re ⟪y, H z⟫_𝕜 + RCLike.re ⟪z, H y⟫_𝕜) := by
  simp only [map_add, LinearMap.map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  ring

end LinearMap

namespace TauCeti

/-- Squared norm of a real linear combination of two vectors orthogonal with respect
to the real part of the inner product. -/
theorem norm_smul_add_smul_sq {y z : E} (hyz : RCLike.re ⟪y, z⟫_𝕜 = 0) (γ σ : ℝ) :
    ‖(γ : 𝕜) • y + (σ : 𝕜) • z‖ ^ 2 = γ ^ 2 * ‖y‖ ^ 2 + σ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜)]
  simp [inner_smul_left, inner_smul_right, hyz, norm_smul, mul_pow, sq_abs]

end TauCeti
