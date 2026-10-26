/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Directional derivatives

For a function `f : 𝕜 → F` of one variable, the directional derivative in the direction `1` is
the ordinary derivative. This identifies the weak directional derivatives of
`TauCeti.HasWeakLineDerivOn` on the real line with one-variable derivatives.

Outside the topological support of a function, its directional derivatives vanish. This is the
directional counterpart of Mathlib's `fderiv_of_notMem_tsupport`. Both results require no
differentiability hypothesis, which matters for Lipschitz functions.
-/

public section

namespace TauCeti

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The directional derivative of a function of one variable in the direction `1` is its
derivative. No differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_one {f : 𝕜 → F} {x : 𝕜} : lineDeriv 𝕜 f x 1 = deriv f x := by
  simp [lineDeriv, deriv_comp_const_add]

/-- Outside the topological support of `f`, every directional derivative of `f` vanishes. No
differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_of_notMem_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → F} {x : E} (h : x ∉ tsupport f) (v : E) : lineDeriv 𝕜 f x v = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.1 h).lineDeriv_eq]
  simp [lineDeriv]

end TauCeti
