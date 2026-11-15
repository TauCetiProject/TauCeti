/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Principal square roots of real linear forms on the upper half-plane

For real `m` and `n`, the principal square root of `m τ + n` is continuous on the upper
half-plane: `m τ + n` is constant if `m = 0`, and otherwise stays off the real axis, where the
branch cut lies. For an integer matrix `(a b; c d)` this is the square root `√(c τ + d)` of its
automorphy factor, as in half-integral-weight transformation laws.

## Main results

* `UpperHalfPlane.continuous_sqrt_ofReal_mul_add`: `τ ↦ √(m τ + n)` is continuous on `ℍ`.
-/

public section

open Complex

open scoped UpperHalfPlane

namespace UpperHalfPlane

/-- The principal square root of a real linear combination `m τ + n` is continuous on the upper
half-plane: it is constant if `m = 0`, and otherwise `m τ + n` stays off the real axis. -/
theorem continuous_sqrt_ofReal_mul_add (m n : ℝ) :
    Continuous fun τ : ℍ ↦ Complex.sqrt ((m : ℂ) * τ + n) := by
  by_cases hm : m = 0
  · simp only [hm, ofReal_zero, zero_mul, zero_add]
    exact continuous_const
  refine continuous_iff_continuousAt.2 fun τ ↦ ?_
  have him : ((m : ℂ) * τ + n).im ≠ 0 := by
    simpa [hm] using τ.im_pos.ne'
  exact (continuousAt_sqrt (Or.inr him)).comp
    (f := fun τ : ℍ ↦ (m : ℂ) * τ + n) (by fun_prop)

end UpperHalfPlane

end
