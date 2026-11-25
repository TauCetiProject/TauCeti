/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Inner products pulled back along linear isometries

A normed space `E` that embeds linearly and isometrically in an inner product space `F`, by
`ι : E →ₗᵢ[𝕜] F`, carries the inner product `⟪x, y⟫ = ⟪ι x, ι y⟫`, whose norm is the given norm of
`E` (`InnerProductSpace.ofLinearIsometry`). Unlike Mathlib's `InnerProductSpace.induced`, which
replaces the norm of `E` by the one induced from `F`, this keeps the normed structure of `E`, so
everything already stated about `E` as a normed space is unchanged.

The typical embedding is the second factor of a Euclidean product: a linear isometry equivalence
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` restricts to `y ↦ e⁻¹ (0, y)`
(`LinearIsometryEquiv.sndLinearIsometry`). This is how the tangential model `E` of a boundary chart
of a domain in an inner product space `F` inherits an inner product, and with it the Euclidean
structure the model-space theory of Lipschitz domains needs.

## Main declarations

* `InnerProductSpace.ofLinearIsometry`: the pulled-back inner product, with
  `InnerProductSpace.inner_ofLinearIsometry`.
* `LinearIsometryEquiv.sndLinearIsometry`: the second factor of `WithLp 2 (ℝ × E)` inside `F`.
-/

public section

noncomputable section

namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The inner product `⟪x, y⟫ = ⟪ι x, ι y⟫` that a linear isometry `ι : E →ₗᵢ[𝕜] F` into an inner
product space induces on `E`. Its norm is the given norm of `E`.

See note [reducible non-instances]. -/
abbrev ofLinearIsometry (ι : E →ₗᵢ[𝕜] F) : InnerProductSpace 𝕜 E where
  inner x y := inner 𝕜 (ι x) (ι y)
  norm_sq_eq_re_inner x := by
    rw [← ι.norm_map x]
    exact norm_sq_eq_re_inner (ι x)
  conj_inner_symm x y := inner_conj_symm (ι x) (ι y)
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]

theorem inner_ofLinearIsometry (ι : E →ₗᵢ[𝕜] F) (x y : E) :
    letI := ofLinearIsometry ι
    inner 𝕜 x y = inner 𝕜 (ι x) (ι y) :=
  rfl

end InnerProductSpace

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The second factor of `WithLp 2 (ℝ × E)` inside `F`: the linear isometry `y ↦ e⁻¹ (0, y)`. -/
def sndLinearIsometry (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) : E →ₗᵢ[ℝ] F where
  toLinearMap := e.symm.toLinearEquiv.toLinearMap.comp
    ((WithLp.linearEquiv 2 ℝ (ℝ × E)).symm.toLinearMap.comp (LinearMap.inr ℝ ℝ E))
  norm_map' y := by simp

@[simp]
theorem sndLinearIsometry_apply (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) (y : E) :
    e.sndLinearIsometry y = e.symm (WithLp.toLp 2 (0, y)) :=
  (rfl)

end LinearIsometryEquiv
