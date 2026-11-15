/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Path.Extend.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives of extended concatenated paths

Away from the joining parameter `1/2`, the derivative is twice the derivative of the
corresponding component at its rescaled parameter. No differentiability assumption is needed:
these formulas use Mathlib's total derivative, which is zero at nondifferentiability points.
They follow from the local concatenation identities and affine derivative composition.
-/

public section

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q r : E}
    (γ : Path p q) (δ : Path q r) {t : ℝ}

/-- Below the joining parameter, the derivative comes from the first path at twice the speed. -/
theorem deriv_extend_trans_of_lt_half (ht : t < 1 / 2) :
    deriv (γ.trans δ).extend t = (2 : ℝ) • deriv γ.extend (2 * t) := by
  rw [(γ.eventuallyEq_extend_trans_of_lt_half δ ht).deriv_eq]
  exact deriv_comp_mul_left 2 γ.extend t

/-- Above the joining parameter, the derivative comes from the second path at twice the speed. -/
theorem deriv_extend_trans_of_half_lt (ht : 1 / 2 < t) :
    deriv (γ.trans δ).extend t = (2 : ℝ) • deriv δ.extend (2 * t - 1) := by
  rw [(γ.eventuallyEq_extend_trans_of_half_lt δ ht).deriv_eq]
  simpa only [deriv_comp_sub_const] using
    (deriv_comp_mul_left 2 (fun x : ℝ ↦ δ.extend (x - 1)) t)

end Path
