/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Bounds on derivative norms

A uniform upper bound on the norm of a real-valued function's Fréchet derivative is
nonnegative. This supplies the sign condition used in estimates involving that bound.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform upper bound on the derivative norm is nonnegative. -/
theorem nonneg_of_forall_norm_fderiv_le {γ : E → ℝ} {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ γ y‖ ≤ L) : 0 ≤ L :=
  (norm_nonneg _).trans (hL 0)

end TauCeti
