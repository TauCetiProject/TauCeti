/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Spanning families of a quadratic algebra

Two elements of a rational quadratic algebra that span it over `ℚ` cannot both have vanishing
imaginary coordinate.
-/

public section

namespace QuadraticAlgebra

/-- Two elements of a rational quadratic algebra whose rational span is everything cannot both
have vanishing imaginary coordinate. -/
theorem im_ne_zero_or_im_ne_zero_of_span_range_eq_top {c d : ℚ} (a : Fin 2 → QuadraticAlgebra ℚ c d)
    (hspan : Submodule.span ℚ (Set.range a) = ⊤) : (a 0).im ≠ 0 ∨ (a 1).im ≠ 0 := by
  by_contra! hzero
  have hω : (omega : QuadraticAlgebra ℚ c d) ∈ Submodule.span ℚ (Set.range a) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hω
  have him := congrArg QuadraticAlgebra.im ht
  simp only [Fin.sum_univ_two, im_add, im_smul, im_omega, smul_eq_mul, hzero.1, hzero.2,
    mul_zero, add_zero] at him
  norm_num at him

end QuadraticAlgebra
