/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The real part of a complex inner product as a real-bilinear map

On a complex inner product space, the real part `Re ⟪x, y⟫` of the inner product is the real inner
product of the underlying real inner product space (`InnerProductSpace.rclikeToReal`). This file
packages it as a continuous real-bilinear map `TauCeti.reInnerCLM`, so the calculus of bounded
bilinear maps applies to `Re ⟪f, g⟫` without installing the real inner product structure as an
instance. It also records `TauCeti.re_inner_smul_eq_real_inner_lsmul`, which rewrites
`Re ⟪c • x, y⟫` as a real inner product against the real-linear map `x ↦ c • x`, and
`TauCeti.real_inner_eq_re_inner_of_norm`, which shows by polarization that any real inner product
sharing the norm of an `RCLike` inner product agrees with its real part.
-/

public section

open Complex
open scoped InnerProductSpace

namespace TauCeti

/-- Any real inner product sharing the norm of an `RCLike` inner product agrees with its real part,
by the polarization identity. -/
theorem real_inner_eq_re_inner_of_norm {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace 𝕜 E] (x y : E) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜 := by
  have h1 := norm_add_sq_real x y
  have h2 := norm_add_sq (𝕜 := 𝕜) x y
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real part `Re ⟪x, y⟫` of a complex inner product, as a continuous real-bilinear map. -/
noncomputable def reInnerCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  letI := InnerProductSpace.rclikeToReal ℂ E
  innerSL ℝ

@[simp]
theorem reInnerCLM_apply (x y : E) : reInnerCLM x y = re ⟪x, y⟫_ℂ :=
  (rfl)

/-- For the real inner product `InnerProductSpace.complexToReal`, `Re ⟪c • x, y⟫` is the real inner
product of `y` with the real-linear map `ContinuousLinearMap.lsmul ℝ ℂ c` applied to `x`. -/
theorem re_inner_smul_eq_real_inner_lsmul (c : ℂ) (x y : E) :
    letI := InnerProductSpace.complexToReal (G := E)
    re ⟪c • x, y⟫_ℂ = ⟪y, ContinuousLinearMap.lsmul ℝ ℂ c x⟫_ℝ := by
  rw [ContinuousLinearMap.lsmul_apply, real_inner_eq_re_inner ℂ, ← RCLike.re_to_complex,
    inner_re_symm]

end TauCeti
