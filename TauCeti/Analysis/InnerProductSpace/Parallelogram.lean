/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The parallelogram law in `ℝ≥0∞`

Mathlib states the parallelogram law `‖x + y‖² + ‖x - y‖² = 2 (‖x‖² + ‖y‖²)` for the real norm
(`parallelogram_law_with_norm`) and the `ℝ≥0` norm (`parallelogram_law_with_nnnorm`). This file
adds the extended-norm form, the shape in which it enters lower Lebesgue integrals such as energy
integrals, where no integrability side conditions are wanted.

## Main declarations

* `TauCeti.parallelogram_law_with_enorm`: the parallelogram law for `‖·‖ₑ`.
-/

public section

namespace TauCeti

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜 in
/-- **The parallelogram law** for the extended norm of an inner product space. -/
theorem parallelogram_law_with_enorm (x y : E) :
    ‖x + y‖ₑ ^ 2 + ‖x - y‖ₑ ^ 2 = 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  simp only [enorm_eq_nnnorm]
  exact_mod_cast congrArg ((↑) : NNReal → ENNReal) (parallelogram_law_with_nnnorm 𝕜 x y)

end TauCeti
