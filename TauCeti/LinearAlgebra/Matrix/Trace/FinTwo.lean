/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo

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

Every power of `A` is a combination `a • A - b • 1`, whose discriminant is `a ^ 2` times that of
`A`; so if `|trace A| ≤ 2` and `det A = 1` then `|trace (A ^ n)| ≤ 2` for every `n`. Since
`det (1 - A ^ n) = 2 - trace (A ^ n)` for determinant one, this gives the sign of `det (1 - A ^ n)`,
which decides whether `1` is an eigenvalue of `A ^ n`, for all iterates at once: it is negative for
`2 < trace A`, alternates as `(-1) ^ (n + 1)` for `trace A < -2`, and is nonnegative for
`|trace A| ≤ 2`.

The **Fricke trace identity** expresses the trace of a commutator in `SL(2, R)` through the traces
of the two matrices and of their product:
`tr ⁅A, B⁆ = tr A ^ 2 + tr B ^ 2 + tr (A B) ^ 2 - tr A tr B tr (A B) - 2`. Alternatively, the
trace of a commutator differs from `2` by minus the determinant of the additive commutator:
`tr ⁅A, B⁆ - 2 = -det (A B - B A)`, since `⁅A, B⁆ - 1 = (A B - B A) A⁻¹ B⁻¹` and
`det (M - 1) = 2 - tr M` for `M ∈ SL(2, R)`.

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
* `Matrix.exists_pow_eq_smul_sub_smul_one_fin_two`, `Matrix.discr_smul_sub_smul_one_fin_two`,
  `Matrix.exists_discr_pow_eq_sq_mul_fin_two`: the powers of a `2 × 2` matrix are combinations of
  the matrix and `1`, and their discriminants are square multiples of its discriminant.
* `Matrix.abs_trace_pow_le_two`: the powers of a determinant-one matrix of trace at most `2` in
  absolute value again have this property.
* `Matrix.det_one_sub_pow_neg_of_two_lt_trace`, `Matrix.det_one_sub_pow_neg_of_trace_lt_neg_two`,
  `Matrix.det_one_sub_pow_pos_of_trace_lt_neg_two`,
  `Matrix.det_one_sub_pow_nonneg_of_abs_trace_le_two`: the sign of `det (1 - A ^ n)` for a
  determinant-one matrix `A`, according to its trace.
* `Matrix.isHyperbolic_iff_two_lt_abs_trace`: a determinant-one matrix is hyperbolic exactly when
  its trace has absolute value greater than `2`.
* `Matrix.isElliptic_iff_abs_trace_lt_two`: a determinant-one matrix is elliptic exactly when its
  trace has absolute value less than `2`.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_fin_two`: the Fricke trace identity.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_sub_two_fin_two`: the trace of a commutator
  through the determinant of the additive commutator.

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

/-- Every power of a `2 × 2` matrix `A` is a linear combination `a • A - b • 1` of `A` and `1`, by
the Cayley–Hamilton identity in size two. -/
theorem exists_pow_eq_smul_sub_smul_one_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    ∃ a b : R, A ^ n = a • A - b • 1 := by
  induction n with
  | zero => exact ⟨0, -1, by simp⟩
  | succ n ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨a * A.trace - b, a * A.det, ?_⟩
    rw [pow_succ, h, sub_mul, smul_mul_assoc, ← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two,
      smul_mul_assoc, one_mul]
    module

/-- The discriminant of the `2 × 2` matrix `a • A - b • 1` is `a ^ 2` times that of `A`. -/
theorem discr_smul_sub_smul_one_fin_two (A : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    (a • A - b • 1).discr = a ^ 2 * A.discr := by
  simp only [discr_fin_two, TauCeti.Matrix.det_smul_sub_smul_one_fin_two, trace_sub, trace_smul,
    trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- The discriminant of a power of a `2 × 2` matrix `A` is a square multiple of the discriminant
of `A`. In particular a power of an elliptic matrix is not hyperbolic, and a power of a hyperbolic
matrix is not elliptic. -/
theorem exists_discr_pow_eq_sq_mul_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    ∃ a : R, (A ^ n).discr = a ^ 2 * A.discr := by
  obtain ⟨a, b, h⟩ := exists_pow_eq_smul_sub_smul_one_fin_two A n
  exact ⟨a, by rw [h, discr_smul_sub_smul_one_fin_two]⟩

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

/-- A `2 × 2` matrix of determinant one is elliptic, in the sense of `Matrix.IsElliptic`, exactly
when its trace has absolute value less than `2`: its discriminant is `trace A ^ 2 - 4`. -/
theorem isElliptic_iff_abs_trace_lt_two {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1) :
    A.IsElliptic ↔ |A.trace| < 2 := by
  rw [IsElliptic, discr_fin_two, hdet, mul_one, sub_neg, show (4 : R) = 2 ^ 2 by norm_num,
    sq_lt_sq, abs_two]

/-- If a `2 × 2` matrix of determinant one has trace of absolute value at most `2`, then so does
every power of it. -/
theorem abs_trace_pow_le_two {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1)
    (htr : |A.trace| ≤ 2) (n : ℕ) : |(A ^ n).trace| ≤ 2 := by
  obtain ⟨a, ha⟩ := exists_discr_pow_eq_sq_mul_fin_two A n
  rw [discr_fin_two, discr_fin_two, det_pow, hdet, one_pow] at ha
  have hA : A.trace ^ 2 ≤ 2 ^ 2 := sq_le_sq.2 (by rwa [abs_two])
  have hle : (A ^ n).trace ^ 2 ≤ 2 ^ 2 := by nlinarith [sq_nonneg a]
  simpa using sq_le_sq.1 hle

/-- If a `2 × 2` matrix `A` of determinant one has trace greater than `2`, then
`det (1 - A ^ n) < 0` for every `n ≠ 0`. -/
theorem det_one_sub_pow_neg_of_two_lt_trace {A : Matrix (Fin 2) (Fin 2) R} (hdet : A.det = 1)
    (htr : 2 < A.trace) {n : ℕ} (hn : n ≠ 0) : (1 - A ^ n).det < 0 := by
  rw [det_one_sub_fin_two, det_pow, hdet, one_pow]
  linarith [two_lt_trace_pow hdet htr hn]

/-- If a `2 × 2` matrix `A` of determinant one has trace less than `-2`, then
`det (1 - A ^ n) < 0` for every even `n ≠ 0`. -/
theorem det_one_sub_pow_neg_of_trace_lt_neg_two {A : Matrix (Fin 2) (Fin 2) R}
    (hdet : A.det = 1) (htr : A.trace < -2) {n : ℕ} (hn : Even n) (hn₀ : n ≠ 0) :
    (1 - A ^ n).det < 0 := by
  rw [← hn.neg_pow]
  exact det_one_sub_pow_neg_of_two_lt_trace (by simp [det_neg, hdet])
    (by rw [trace_neg]; linarith) hn₀

/-- If a `2 × 2` matrix `A` of determinant one has trace less than `-2`, then
`0 < det (1 - A ^ n)` for every odd `n`. -/
theorem det_one_sub_pow_pos_of_trace_lt_neg_two {A : Matrix (Fin 2) (Fin 2) R}
    (hdet : A.det = 1) (htr : A.trace < -2) {n : ℕ} (hn : Odd n) : 0 < (1 - A ^ n).det := by
  -- `A ^ n = -(-A) ^ n`, and the trace of `(-A) ^ n` is greater than `2`.
  have h := two_lt_trace_pow (A := -A) (by simp [det_neg, hdet]) (by rw [trace_neg]; linarith)
    (n := n) (by rintro rfl; simp at hn)
  rw [hn.neg_pow, trace_neg] at h
  rw [det_one_sub_fin_two, det_pow, hdet, one_pow]
  linarith

/-- If a `2 × 2` matrix `A` of determinant one has trace of absolute value at most `2`, then
`0 ≤ det (1 - A ^ n)` for every `n`. -/
theorem det_one_sub_pow_nonneg_of_abs_trace_le_two {A : Matrix (Fin 2) (Fin 2) R}
    (hdet : A.det = 1) (htr : |A.trace| ≤ 2) (n : ℕ) : 0 ≤ (1 - A ^ n).det := by
  rw [det_one_sub_fin_two, det_pow, hdet, one_pow]
  linarith [(abs_le.1 (abs_trace_pow_le_two hdet htr n)).2]

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

open scoped commutatorElement MatrixGroups in
/-- The trace of the commutator `A * B * A⁻¹ * B⁻¹` of two matrices of `SL(2, R)` differs from `2`
by minus the determinant of their additive commutator: `tr ⁅A, B⁆ - 2 = -det (A B - B A)`. -/
theorem SpecialLinearGroup.trace_commutatorElement_sub_two_fin_two {R : Type*} [CommRing R]
    (A B : SL(2, R)) :
    ((⁅A, B⁆ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace - 2 =
      -((A : Matrix (Fin 2) (Fin 2) R) * B - B * A).det := by
  have hA := A.det_coe
  have hB := B.det_coe
  rw [det_fin_two] at hA hB
  simp only [commutatorElement_def, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
    adjugate_fin_two, trace_fin_two, det_fin_two, sub_apply, mul_apply, Fin.sum_univ_two, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  linear_combination 2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0) * hB + 2 * hA

end Matrix
