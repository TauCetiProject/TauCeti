/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Complex conjugation: invariant discs, symmetric norms and unit-norm quotients

Complex conjugation is an isometry fixing the real axis (Mathlib's `Complex.dist_conj_conj`), so
it maps every open or closed disc centred on the real axis to itself. Such discs are the natural
domains for reflection across the real axis, for instance the even reflection
`TauCeti.evenReflection`.

Conjugation also preserves norms (Mathlib's `Complex.norm_conj`), so the norm of
`1 - conj w * z` is symmetric in `z` and `w` (`Complex.norm_one_sub_conj_mul_comm`). This
expression is the denominator of the Möbius automorphisms of the unit disc and of the
pseudo-hyperbolic expression.

The scalar Cayley expression `1 + (z - conj z) / (r - z)` has unit norm for real `r`.
When `z ≠ r`, it is the quotient `(r - conj z) / (r - z)` of a complex number's conjugate
by itself; at `z = r`, Lean's totalized inverse gives value one.
-/

public section

open scoped ComplexConjugate

/-- The scalar Cayley expression has unit norm at real `r`, including when `z = r`
under the totalized inverse convention. -/
theorem Complex.norm_one_add_sub_conj_mul_inv_ofReal_sub (z : ℂ) (r : ℝ) :
    ‖1 + (z - conj z) * ((r : ℂ) - z)⁻¹‖ = 1 := by
  by_cases hne : (r : ℂ) - z = 0
  · simp [hne]
  have heq : 1 + (z - conj z) * ((r : ℂ) - z)⁻¹ =
      ((r : ℂ) - conj z) / ((r : ℂ) - z) := by
    field_simp
    ring
  have hnorm : ‖(r : ℂ) - conj z‖ = ‖(r : ℂ) - z‖ := by
    simpa using Complex.norm_conj ((r : ℂ) - z)
  rw [heq, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hne)]

namespace TauCeti

open ComplexConjugate Metric

variable {x₀ z : ℂ} {r : ℝ}

/-- Conjugation maps an open disc centred on the real axis to itself. -/
theorem conj_mem_ball_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ ball x₀ r) :
    conj z ∈ ball x₀ r := by
  rwa [mem_ball, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Conjugation maps a closed disc centred on the real axis to itself. -/
theorem conj_mem_closedBall_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ closedBall x₀ r) :
    conj z ∈ closedBall x₀ r := by
  rwa [mem_closedBall, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

end TauCeti

namespace Complex

open ComplexConjugate

/-- The norm of `1 - conj w * z` is symmetric in `z` and `w`: conjugation swaps the two
expressions and preserves norms. -/
theorem norm_one_sub_conj_mul_comm (z w : ℂ) : ‖1 - conj w * z‖ = ‖1 - conj z * w‖ := by
  rw [← norm_conj]
  simp [mul_comm]

end Complex
