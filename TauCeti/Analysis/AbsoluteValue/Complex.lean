/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Absolute values on `ℂ` extending the absolute value of `ℝ`

An absolute value on `ℂ` whose restriction to `ℝ` is the usual absolute value is the complex
norm. No continuity is assumed. Such an absolute value is a multiplicative `ℝ`-algebra norm on `ℂ`,
and these are unique over the complete field `ℝ` by `MulAlgebraNorm.unique`.

This is what turns an `ℝ`-algebra isomorphism of a normed field with `ℂ`, as produced by the
Gelfand–Mazur theorem, into an isometry.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` agreeing with `|·|` on `ℝ` is
  the complex norm.
-/

public section

namespace AbsoluteValue

/-- An absolute value on `ℂ` that restricts to the usual absolute value on `ℝ` is the complex
norm. -/
theorem eq_norm_of_apply_ofReal (N : AbsoluteValue ℂ ℝ) (h : ∀ r : ℝ, N r = |r|) (z : ℂ) :
    N z = ‖z‖ := by
  let f : MulAlgebraNorm ℝ ℂ :=
    { toFun := N
      map_zero' := N.map_zero
      add_le' := N.add_le
      neg' := N.map_neg
      map_one' := N.map_one
      map_mul' := N.map_mul
      eq_zero_of_map_eq_zero' _ := N.eq_zero.mp
      smul' r x := by rw [Complex.real_smul, map_mul, h, Real.norm_eq_abs] }
  exact congr($(MulAlgebraNorm.unique f (NormedAlgebra.toMulAlgebraNorm ℝ ℂ)) z)

end AbsoluteValue
