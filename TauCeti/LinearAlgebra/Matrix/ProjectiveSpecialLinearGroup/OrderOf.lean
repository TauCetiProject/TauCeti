/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Matrix.TraceFinTwo
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Orders of elements of `PSL(2)` read off from the trace

The trace of a matrix of `SL(2, R)` is determined up to sign by its class in
`PSL(2, R) = SL(2, R) ⧸ {±1}`, and it controls the order of that class:

* an element of `PSL(2, ℝ)` whose representatives have trace `± 2 cos (π / k)`, with `2 ≤ k`,
  is elliptic of order dividing `k`;
* over a linearly ordered commutative ring, an element of `PSL(2, R)` whose representatives have
  trace of absolute value greater than `2` — a hyperbolic element — has infinite order.

The matrix computations behind both statements are in `TauCeti.LinearAlgebra.Matrix.TraceFinTwo`.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq`: if
  `trace A ^ 2 = (2 cos (π / k)) ^ 2` with `2 ≤ k`, then the class of `A` has `k`-th power `1`.
* `Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_two_lt_abs_trace`: if
  `2 < |trace A|`, then the class of `A` has infinite order.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1.
-/

public section

open Real
open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

/-- If a matrix of `SL(2, ℝ)` has trace `± 2 cos (π / k)` with `2 ≤ k`, then its class in
`PSL(2, ℝ)` has `k`-th power `1`: the matrix itself, or its negative, has `k`-th power `-1`. The
hypothesis is stated on the square of the trace, which depends only on the class in `PSL(2, ℝ)`. -/
theorem mk_pow_eq_one_of_trace_sq_eq {A : SL(2, ℝ)} {k : ℕ} (hk : 2 ≤ k)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = (2 * cos (π / k)) ^ 2) :
    (A : PSL(2, ℝ)) ^ k = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact .inr (Subtype.ext (by
      rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one]
      exact pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div A.det_coe hk h))
  · -- The negative of `A` has trace `2 cos (π / k)`, and `(-A) ^ k = ± A ^ k`.
    have hneg := pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div (A := -(A : Matrix _ _ ℝ))
      (by simp [det_neg]) hk (by rw [trace_neg, h, neg_neg])
    rcases k.even_or_odd with hk' | hk'
    · rw [hk'.neg_pow] at hneg
      exact .inr (Subtype.ext (by
        rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one,
          hneg]))
    · rw [hk'.neg_pow, neg_inj] at hneg
      exact .inl (Subtype.ext (by rw [SpecialLinearGroup.coe_pow, hneg,
        SpecialLinearGroup.coe_one]))

/-- A **hyperbolic element of `PSL(2, R)` has infinite order**: if a matrix of `SL(2, R)` has
trace of absolute value greater than `2`, then its class in `PSL(2, R)` has infinite order, since
every nonzero power of the matrix again has trace of absolute value greater than `2`, while `±1`
have trace `±2`. -/
theorem not_isOfFinOrder_mk_of_two_lt_abs_trace {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {A : SL(2, R)}
    (h : 2 < |(A : Matrix (Fin 2) (Fin 2) R).trace|) : ¬ IsOfFinOrder (A : PSL(2, R)) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hpow
  have htr := two_lt_abs_trace_pow A.det_coe h hn.ne'
  rw [← SpecialLinearGroup.coe_pow] at htr
  rcases hpow with hpow | hpow <;> simp [hpow] at htr

end Matrix.ProjectiveSpecialLinearGroup
