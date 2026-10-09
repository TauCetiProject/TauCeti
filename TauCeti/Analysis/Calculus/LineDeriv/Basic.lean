/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Directional derivatives in one variable

For a function `f : 𝕜 → F` of one variable, the directional derivative in the direction `1` is
the ordinary derivative. This identifies the weak directional derivatives of
`TauCeti.HasWeakLineDerivOn` on the real line with one-variable derivatives.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The directional derivative of a function of one variable in the direction `1` is its
derivative. No differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_one {f : 𝕜 → F} {x : 𝕜} : lineDeriv 𝕜 f x 1 = deriv f x := by
  simp [lineDeriv, deriv_comp_const_add]
