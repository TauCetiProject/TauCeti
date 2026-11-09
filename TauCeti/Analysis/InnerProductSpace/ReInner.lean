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
instance.
-/

public section

open Complex
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real part `Re ⟪x, y⟫` of a complex inner product, as a continuous real-bilinear map. -/
noncomputable def reInnerCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  letI := InnerProductSpace.rclikeToReal ℂ E
  innerSL ℝ

@[simp]
theorem reInnerCLM_apply (x y : E) : reInnerCLM x y = re ⟪x, y⟫_ℂ :=
  (rfl)

end TauCeti
