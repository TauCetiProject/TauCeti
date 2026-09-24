/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Hyperbolic elements of `PSL(2)` have infinite order

Over a commutative ring without zero divisors the center of `SL(2, R)` is `{±1}`, so
`PSL(2, R) = SL(2, R) ⧸ {±1}` and the trace of a matrix of `SL(2, R)` is determined up to sign by
its class in `PSL(2, R)`. Over a linearly ordered commutative ring, an element of `PSL(2, R)` whose
representatives have trace of absolute value greater than `2` — a hyperbolic element, in the sense
of `Matrix.IsHyperbolic` — has infinite order.

The matrix computations behind this are in `TauCeti.LinearAlgebra.Matrix.Trace.FinTwo`. The
elliptic counterpart over `ℝ`, for traces `± 2 cos (π / k)`, is in
`TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo`.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_two_lt_abs_trace`: if
  `2 < |trace A|`, then the class of `A` has infinite order.
* `Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_isHyperbolic`: the same, for `A`
  hyperbolic in the sense of `Matrix.IsHyperbolic`.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

variable {S : Type*} [CommRing S]

/-- Negating a special linear matrix does not change its class in `PSL(2, S)`. -/
theorem mk_neg (A : SL(2, S)) : ((-A : SL(2, S)) : PSL(2, S)) = A := by
  rw [QuotientGroup.eq_iff_div_mem]
  have h : (-A) / A = (-1 : SL(2, S)) := by
    rw [← neg_one_mul A]
    exact mul_div_cancel_right _ _
  rw [h]
  exact Subgroup.mem_center_iff.mpr fun g ↦ by rw [neg_one_mul, mul_neg_one]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A **hyperbolic element of `PSL(2, R)` has infinite order**: if a matrix of `SL(2, R)` has
trace of absolute value greater than `2`, then its class in `PSL(2, R)` has infinite order, since
every nonzero power of the matrix again has trace of absolute value greater than `2`, while `±1`
have trace `±2`. -/
theorem not_isOfFinOrder_mk_of_two_lt_abs_trace {A : SL(2, R)}
    (h : 2 < |(A : Matrix (Fin 2) (Fin 2) R).trace|) : ¬ IsOfFinOrder (A : PSL(2, R)) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hpow
  have htr := two_lt_abs_trace_pow A.det_coe h hn.ne'
  rw [← SpecialLinearGroup.coe_pow] at htr
  rcases hpow with hpow | hpow <;> simp [hpow] at htr

/-- If a matrix of `SL(2, R)` is hyperbolic, in the sense of `Matrix.IsHyperbolic`, then its class
in `PSL(2, R)` has infinite order. -/
theorem not_isOfFinOrder_mk_of_isHyperbolic {A : SL(2, R)}
    (h : (A : Matrix (Fin 2) (Fin 2) R).IsHyperbolic) : ¬ IsOfFinOrder (A : PSL(2, R)) :=
  not_isOfFinOrder_mk_of_two_lt_abs_trace ((isHyperbolic_iff_two_lt_abs_trace A.det_coe).1 h)

end Matrix.ProjectiveSpecialLinearGroup
