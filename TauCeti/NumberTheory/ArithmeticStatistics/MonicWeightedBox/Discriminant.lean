/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.NumberTheory.ArithmeticStatistics.MonicWeightedBox.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Discriminants of monic quadratics in the weighted box

A monic quadratic `x^2 + a x + b` in `TauCeti.monicWeightedBox 2 X` has discriminant
`discrim 1 a b = a^2 - 4 b` (`TauCeti.discr_eq_discrim_of_mem_monicWeightedBox_two`, the monic
case of `Polynomial.discr_eq_discrim_of_degree_eq_two`). Since `|a| < X` and `|b| < X^2`, its
absolute value is less than `5 X^2` (`TauCeti.abs_discr_lt_of_mem_monicWeightedBox_two`).
-/

public section

open Polynomial

namespace TauCeti

variable {X : ℝ}

/-- A monic quadratic `x^2 + a x + b` in the weighted box has discriminant `discrim 1 a b`. -/
theorem discr_eq_discrim_of_mem_monicWeightedBox_two {f : ℤ[X]}
    (hf : f ∈ monicWeightedBox 2 X) : f.discr = discrim 1 (f.coeff 1) (f.coeff 0) := by
  obtain ⟨hm, hd, -⟩ := mem_monicWeightedBox.mp hf
  have h2 : f.coeff 2 = 1 := hd ▸ hm.coeff_natDegree
  rw [discr_eq_discrim_of_degree_eq_two ((degree_eq_iff_natDegree_eq hm.ne_zero).mpr hd), h2]

/-- A monic quadratic `x^2 + a x + b` with `|a| < X` and `|b| < X^2` has discriminant of absolute
value less than `5 X^2`. -/
theorem abs_discr_lt_of_mem_monicWeightedBox_two {f : ℤ[X]} (hf : f ∈ monicWeightedBox 2 X) :
    |(f.discr : ℝ)| < 5 * X ^ 2 := by
  obtain ⟨-, -, hc⟩ := mem_monicWeightedBox.mp hf
  have h₁ : |(f.coeff 1 : ℝ)| < X := by simpa using hc 1 one_lt_two
  have h₀ : |(f.coeff 0 : ℝ)| < X ^ 2 := by simpa using hc 0 two_pos
  have hsq : (f.coeff 1 : ℝ) ^ 2 < X ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ h₁ (abs_nonneg _) two_ne_zero
  have habs :
      |(f.coeff 1 : ℝ) ^ 2 - 4 * f.coeff 0| ≤ (f.coeff 1 : ℝ) ^ 2 + 4 * |(f.coeff 0 : ℝ)| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos four_pos]
  rw [discr_eq_discrim_of_mem_monicWeightedBox_two hf, discrim]
  push_cast
  linarith

end TauCeti
