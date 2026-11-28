/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The principal logarithm of a quotient

The real part of `log (x / y)` is always `log ‖x‖ - log ‖y‖`, so the quotient rule
`log (x / y) = log x - log y` for the principal logarithm holds exactly when the corresponding
rule `arg (x / y) = arg x - arg y` holds for the principal argument, that is, when
`arg x - arg y ∈ (-π, π]`.

## Main results

* `Complex.log_div_eq_sub_log_iff`: `log (x / y) = log x - log y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.log_div_of_re_pos`: if `0 < x.re` and `0 < y.re`, then `log (x / y) = log x - log y`.
-/

public section

namespace Complex

/-- The principal logarithm of a quotient is the difference of the principal logarithms exactly
when the difference of the arguments lies in `(-π, π]`. -/
theorem log_div_eq_sub_log_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    log (x / y) = log x - log y ↔ arg x - arg y ∈ Set.Ioc (-Real.pi) Real.pi := by
  rw [← arg_div_eq_sub_arg_iff hx₀ hy₀, Complex.ext_iff]
  simp only [log_re, log_im, norm_div, sub_re, sub_im,
    Real.log_div (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

/-- The principal logarithm of the quotient of two points of the open right half-plane is the
difference of their principal logarithms. -/
theorem log_div_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    log (x / y) = log x - log y := by
  have hx₀ : x ≠ 0 := fun h ↦ hx.ne' (by rw [h, zero_re])
  have hy₀ : y ≠ 0 := fun h ↦ hy.ne' (by rw [h, zero_re])
  exact (log_div_eq_sub_log_iff hx₀ hy₀).2 <|
    (arg_div_eq_sub_arg_iff hx₀ hy₀).1 (arg_div_of_re_pos hx hy)

end Complex
