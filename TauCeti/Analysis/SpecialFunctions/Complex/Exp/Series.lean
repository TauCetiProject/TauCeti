/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The exponential series without its constant term

In any complete normed algebra, dropping the constant term `1` of the exponential series gives the
series of `exp x - 1`, re-indexed from `0` (`NormedSpace.hasSum_exp_sub_one`). This file records
its complex form, with `Complex.exp` and multiplication: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`.

## Main results

* `Complex.hasSum_exp_sub_one`: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!` for every complex `z`.
-/

public section

open scoped Nat

namespace Complex

/-- The exponential series without its constant term: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`. -/
theorem hasSum_exp_sub_one (z : ℂ) :
    HasSum (fun n : ℕ ↦ (((n + 1)! : ℂ))⁻¹ * z ^ (n + 1)) (exp z - 1) := by
  simpa only [smul_eq_mul, ← exp_eq_exp_ℂ] using NormedSpace.hasSum_exp_sub_one ℂ z

end Complex
