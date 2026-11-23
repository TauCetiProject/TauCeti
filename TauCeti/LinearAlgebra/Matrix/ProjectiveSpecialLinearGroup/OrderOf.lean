/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Hyperbolic elements of `PSL(2)` have infinite order, and torsion is elliptic

Over a commutative ring without zero divisors the center of `SL(2, R)` is `{±1}`, so
`PSL(2, R) = SL(2, R) ⧸ {±1}` and the trace of a matrix of `SL(2, R)` is determined up to sign by
its class in `PSL(2, R)`. Over a linearly ordered commutative ring, an element of `PSL(2, R)` whose
representatives have trace of absolute value greater than `2` — a hyperbolic element, in the sense
of `Matrix.IsHyperbolic` — has infinite order. Since parabolic elements also have infinite order
(`Matrix.ProjectiveSpecialLinearGroup.IsParabolic.not_isOfFinOrder`), every nontrivial element of
finite order of `PSL(2, R)` has elliptic representatives: their trace has absolute value less
than `2`.

The matrix computations behind this are in `TauCeti.LinearAlgebra.Matrix.Trace.FinTwo`. The
elliptic counterpart over `ℝ`, for traces `± 2 cos (π / k)`, is in
`TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Basic`.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_two_lt_abs_trace`: if
  `2 < |trace A|`, then the class of `A` has infinite order.
* `Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_isHyperbolic`: the same, for `A`
  hyperbolic in the sense of `Matrix.IsHyperbolic`.
* `Matrix.ProjectiveSpecialLinearGroup.isElliptic_of_isOfFinOrder_mk`: a matrix of `SL(2, R)`
  whose class in `PSL(2, R)` is nontrivial of finite order is elliptic.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

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

/-- **Torsion in `PSL(2, R)` is elliptic**: if the class of a matrix `A` of `SL(2, R)` is a
nontrivial element of finite order of `PSL(2, R)`, then `A` is elliptic, that is,
`|trace A| < 2`. A larger trace makes the class hyperbolic, and the trace `± 2` makes it trivial
or parabolic; both hyperbolic and parabolic elements have infinite order. -/
theorem isElliptic_of_isOfFinOrder_mk {A : SL(2, R)} (h : IsOfFinOrder (A : PSL(2, R)))
    (h1 : (A : PSL(2, R)) ≠ 1) : (A : Matrix (Fin 2) (Fin 2) R).IsElliptic := by
  rw [isElliptic_iff_abs_trace_lt_two A.det_coe]
  refine lt_of_not_ge fun hle ↦ ?_
  rcases hle.lt_or_eq with hlt | heq
  · exact not_isOfFinOrder_mk_of_two_lt_abs_trace hlt h
  · have hsq : (A : Matrix (Fin 2) (Fin 2) R).trace ^ 2 = 4 := by
      rw [← sq_abs, ← heq]
      norm_num
    exact (eq_one_or_isParabolic_of_trace_sq_eq_four hsq).elim h1
      fun hp ↦ hp.not_isOfFinOrder h

end Matrix.ProjectiveSpecialLinearGroup
