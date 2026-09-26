/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Matrix.AdjugateFinTwo

/-!
# Trace identities for `2 × 2` matrices

By the Cayley–Hamilton theorem in size two, a `2 × 2` matrix `A` satisfies
`A ^ 2 = (trace A) • A - (det A) • 1`, so its powers obey the linear recurrence
`A ^ (n + 2) = (trace A) • A ^ (n + 1) - (det A) • A ^ n`, and so do their traces. Over a linearly
ordered commutative ring this controls the powers of a hyperbolic matrix of determinant one: if
`2 < trace A` then the traces of the powers of `A` increase strictly, so `2 < trace (A ^ n)` for
every `n ≠ 0`; hence if `2 < |trace A|` then `2 < |trace (A ^ n)|` for every `n ≠ 0`. In particular
no nonzero power of such a matrix is `± 1`. For determinant one, `2 < |trace A|` is equivalent to
Mathlib's `Matrix.IsHyperbolic A`, whose discriminant is `trace A ^ 2 - 4`.

The **Fricke trace identity** expresses the trace of a commutator in `SL(2, R)` through the traces
of the two matrices and of their product:
`tr ⁅A, B⁆ = tr A ^ 2 + tr B ^ 2 + tr (A B) ^ 2 - tr A tr B tr (A B) - 2`.

These are the matrix inputs for reading off the order of an element of `SL(2, R)` or `PSL(2, R)`
from its trace, and for recognizing a commutator as hyperbolic. The real elliptic case, where the
trace is `2 cos θ`, is in `TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo`.

## Main results

* `Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two`: the Cayley–Hamilton identity in size two.
* `Matrix.pow_add_two_fin_two`, `Matrix.trace_pow_add_two_fin_two`: the Cayley–Hamilton recurrence
  for the powers of a `2 × 2` matrix and for their traces.
* `Matrix.two_lt_trace_pow`, `Matrix.two_lt_abs_trace_pow`: the nonzero powers of a
  determinant-one matrix of trace (respectively absolute trace) greater than `2` again have that
  property.
* `Matrix.isHyperbolic_iff_two_lt_abs_trace`: a determinant-one matrix is hyperbolic exactly when
  its trace has absolute value greater than `2`.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_fin_two`: the Fricke trace identity.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1 (the classification of elements of `PSL(2, ℝ)` by their trace).
* William M. Goldman, *Trace coordinates on Fricke spaces of some simple hyperbolic surfaces*,
  in *Handbook of Teichmüller theory, Vol. II*, EMS, 2009, §2 (the trace of a commutator).
-/

public section

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R]

/-- **Cayley–Hamilton in size two**: a `2 × 2` matrix `A` satisfies
`A ^ 2 = (trace A) • A - (det A) • 1`. -/
theorem sq_eq_trace_smul_sub_det_smul_one_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 = A.trace • A - A.det • 1 := by
  have h := A.mul_adjugate
  rw [adjugate_fin_two_eq_trace_smul_one_sub, mul_sub, Matrix.mul_smul, mul_one] at h
  rw [sq, ← h, sub_sub_cancel]

/-- **Cayley–Hamilton in size two**, as a recurrence for the powers of a `2 × 2` matrix. -/
theorem pow_add_two_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    A ^ (n + 2) = A.trace • A ^ (n + 1) - A.det • A ^ n := by
  rw [pow_add, sq_eq_trace_smul_sub_det_smul_one_fin_two, mul_sub, Matrix.mul_smul,
    Matrix.mul_smul, mul_one, pow_succ]

/-- The traces of the powers of a `2 × 2` matrix satisfy the Cayley–Hamilton recurrence. -/
theorem trace_pow_add_two_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (A ^ (n + 2)).trace = A.trace * (A ^ (n + 1)).trace - A.det * (A ^ n).trace := by
  rw [pow_add_two_fin_two, trace_sub, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]

end CommRing

section Ordered

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If a `2 × 2` matrix of determinant one has trace greater than `2`, then so does every nonzero
power of it: the traces of the powers increase strictly. -/
theorem two_lt_trace_pow {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1) (htr : 2 < A.trace)
    {n : ℕ} (hn : n ≠ 0) : 2 < (A ^ n).trace := by
  have key (m : ℕ) : 2 ≤ (A ^ m).trace ∧ (A ^ m).trace < (A ^ (m + 1)).trace := by
    induction m with
    | zero => simpa using htr
    | succ m ih =>
      refine ⟨ih.1.trans ih.2.le, ?_⟩
      rw [trace_pow_add_two_fin_two, hdet, one_mul]
      nlinarith [ih.1, ih.2]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact (key m).1.trans_lt (key m).2

/-- If a `2 × 2` matrix of determinant one has trace of absolute value greater than `2`, then so
does every nonzero power of it. In particular no nonzero power of it is `1` or `-1`. -/
theorem two_lt_abs_trace_pow {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1)
    (htr : 2 < |A.trace|) {n : ℕ} (hn : n ≠ 0) : 2 < |(A ^ n).trace| := by
  rcases lt_abs.mp htr with h | h
  · exact (two_lt_trace_pow hdet h hn).trans_le (le_abs_self _)
  · -- Apply the positive case to `-A`, whose powers are `± A ^ n`.
    have h' := two_lt_trace_pow (A := -A) (by simp [det_neg, hdet]) (by simpa using h) hn
    rcases n.even_or_odd with hn' | hn'
    · rw [hn'.neg_pow] at h'
      exact h'.trans_le (le_abs_self _)
    · rw [hn'.neg_pow, trace_neg] at h'
      exact h'.trans_le (neg_le_abs _)

/-- A `2 × 2` matrix of determinant one is hyperbolic, in the sense of `Matrix.IsHyperbolic`,
exactly when its trace has absolute value greater than `2`: its discriminant is
`trace A ^ 2 - 4`. -/
theorem isHyperbolic_iff_two_lt_abs_trace {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1) :
    A.IsHyperbolic ↔ 2 < |A.trace| := by
  rw [IsHyperbolic, discr_fin_two, hdet, mul_one, sub_pos, show (4 : R) = 2 ^ 2 by norm_num,
    sq_lt_sq, abs_two]

end Ordered

open scoped commutatorElement MatrixGroups in
/-- The **Fricke trace identity**: the trace of the commutator `A * B * A⁻¹ * B⁻¹` of two matrices
of `SL(2, R)` is `tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 - tr A * tr B * tr (A * B) - 2`. -/
theorem SpecialLinearGroup.trace_commutatorElement_fin_two {R : Type*} [CommRing R]
    (A B : SL(2, R)) :
    ((⁅A, B⁆ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace =
      (A : Matrix (Fin 2) (Fin 2) R).trace ^ 2 + (B : Matrix (Fin 2) (Fin 2) R).trace ^ 2 +
        ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace ^ 2 -
        (A : Matrix (Fin 2) (Fin 2) R).trace * (B : Matrix (Fin 2) (Fin 2) R).trace *
          ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace - 2 := by
  have hA := A.det_coe
  have hB := B.det_coe
  rw [det_fin_two] at hA hB
  simp only [commutatorElement_def, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
    adjugate_fin_two, trace_fin_two, mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  linear_combination ((B 0 0 + B 1 1) ^ 2 - 2) * hA +
    (A 0 0 ^ 2 + 2 * A 0 1 * A 1 0 + A 1 1 ^ 2) * hB

end Matrix
