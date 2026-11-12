/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal complements and projections under restriction of scalars

A complex inner product space `E` is a real inner product space for the inner product
`re ⟪x, y⟫` (`InnerProductSpace.complexToReal`). This file compares the two orthogonality
relations on complex subspaces. For a complex subspace `K`, a vector is real-orthogonal to `K`
exactly when it is complex-orthogonal to `K`, since `K` is stable under multiplication by `I`.
Consequently the real orthogonal complement of `K` is again a complex subspace, and the real and
complex orthogonal projections onto `K` agree.

The real inner product is not a global instance in Mathlib, so it is enabled locally here; the
statements below are about that real structure.

## Main results

* `Submodule.orthogonal_restrictScalars`: `(K.restrictScalars ℝ)ᗮ = Kᗮ.restrictScalars ℝ`.
* `Submodule.starProjection_restrictScalars_apply`: the real orthogonal projection onto `K` is the
  complex one.
-/

public section

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

attribute [local instance] InnerProductSpace.complexToReal

/-- For the real inner product `re ⟪x, y⟫`, the orthogonal complement of a complex subspace is
the complex orthogonal complement. In particular it is stable under multiplication by `I`. -/
@[simp]
theorem orthogonal_restrictScalars (K : Submodule ℂ E) :
    (K.restrictScalars ℝ)ᗮ = Kᗮ.restrictScalars ℝ := by
  ext v
  rw [restrictScalars_mem, mem_orthogonal_iff_re_inner_eq_zero (K := K), mem_orthogonal]
  simp only [restrictScalars_mem, real_inner_eq_re_inner]

/-- A complex subspace admitting a complex orthogonal projection admits a real one. -/
instance HasOrthogonalProjection.restrictScalars (K : Submodule ℂ E) [K.HasOrthogonalProjection] :
    (K.restrictScalars ℝ).HasOrthogonalProjection where
  exists_orthogonal v := by
    obtain ⟨w, hw, hvw⟩ := HasOrthogonalProjection.exists_orthogonal (K := K) v
    exact ⟨w, hw, by rwa [orthogonal_restrictScalars]⟩

/-- The real orthogonal projection onto a complex subspace is the complex orthogonal projection. -/
@[simp]
theorem starProjection_restrictScalars_apply (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (v : E) : (K.restrictScalars ℝ).starProjection v = K.starProjection v := by
  refine eq_starProjection_of_mem_of_inner_eq_zero (K := K.restrictScalars ℝ)
    (K.starProjection_apply_mem v) fun w hw ↦ ?_
  rw [real_inner_eq_re_inner, K.starProjection_inner_eq_zero v w hw, map_zero]

end Submodule
