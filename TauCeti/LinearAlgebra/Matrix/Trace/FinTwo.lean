/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace identities for `2 × 2` matrices

By the Cayley–Hamilton theorem in size two, a `2 × 2` matrix `A` satisfies
`A ^ 2 = (trace A) • A - (det A) • 1`, so its powers obey the linear recurrence
`A ^ (n + 2) = (trace A) • A ^ (n + 1) - (det A) • A ^ n`, and so do their traces. For a matrix
of determinant one this pins down the order behaviour in terms of the trace alone:

* **Elliptic case.** If `trace A = 2 cos θ`, then
  `sin θ • A ^ n = sin (n θ) • A - sin ((n - 1) θ) • 1` (the Chebyshev form of the recurrence).
  At `θ = π / k` with `2 ≤ k` this gives `A ^ k = -1`.
* **Hyperbolic case.** Over a linearly ordered commutative ring, if `2 < trace A` then the traces
  of the powers of `A` increase strictly, so `2 < trace (A ^ n)` for every `n ≠ 0`; hence if
  `2 < |trace A|` then `2 < |trace (A ^ n)|` for every `n ≠ 0`. In particular no nonzero power of
  such a matrix is `± 1`.

The **Fricke trace identity** expresses the trace of a commutator in `SL(2, R)` through the traces
of the two matrices and of their product:
`tr ⁅A, B⁆ = tr A ^ 2 + tr B ^ 2 + tr (A B) ^ 2 - tr A tr B tr (A B) - 2`.

These are the matrix inputs for reading off the order of an element of `SL(2, ℝ)` or `PSL(2, ℝ)`
from its trace, and for recognizing a commutator as hyperbolic.

## Main results

* `Matrix.pow_add_two_fin_two`, `Matrix.trace_pow_add_two_fin_two`: the Cayley–Hamilton recurrence
  for the powers of a `2 × 2` matrix and for their traces.
* `Matrix.sin_smul_pow_fin_two`: the powers of a determinant-one matrix of trace `2 cos θ`.
* `Matrix.pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div`: a determinant-one real matrix of trace
  `2 cos (π / k)`, with `2 ≤ k`, has `k`-th power `-1`.
* `Matrix.two_lt_trace_pow`, `Matrix.two_lt_abs_trace_pow`: the powers of a determinant-one matrix
  of trace (respectively absolute trace) greater than `2` again have that property.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_fin_two`: the Fricke trace identity.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1 (the classification of elements of `PSL(2, ℝ)` by their trace).
* William M. Goldman, *Trace coordinates on Fricke spaces of some simple hyperbolic surfaces*,
  in *Handbook of Teichmüller theory, Vol. II*, EMS, 2009, §2 (the trace of a commutator).
-/

public section

open Real

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R]

/-- **Cayley–Hamilton in size two**, as a recurrence for the powers of a `2 × 2` matrix. -/
theorem pow_add_two_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    A ^ (n + 2) = A.trace • A ^ (n + 1) - A.det • A ^ n := by
  have h : A ^ 2 = A.trace • A - A.det • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring
  rw [pow_add, h, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, pow_succ]

/-- The traces of the powers of a `2 × 2` matrix satisfy the Cayley–Hamilton recurrence. -/
theorem trace_pow_add_two_fin_two (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (A ^ (n + 2)).trace = A.trace * (A ^ (n + 1)).trace - A.det * (A ^ n).trace := by
  rw [pow_add_two_fin_two, trace_sub, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]

end CommRing

/-- The powers of a real `2 × 2` matrix of determinant one and trace `2 cos θ`:
`sin θ • A ^ n = sin (n θ) • A - sin ((n - 1) θ) • 1`. The coefficients are the values of the
Chebyshev polynomials of the second kind at `cos θ`, multiplied by `sin θ`. -/
theorem sin_smul_pow_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ} {θ : ℝ} (hdet : A.det = 1)
    (htr : A.trace = 2 * cos θ) (n : ℕ) :
    sin θ • A ^ n = sin (n * θ) • A - sin ((n - 1) * θ) • 1 := by
  -- The sine sequence obeys the same recurrence as the powers:
  -- `sin ((m + 1) θ) = 2 cos θ sin (m θ) - sin ((m - 1) θ)`.
  have hsin (m : ℝ) : sin ((m + 1) * θ) = 2 * cos θ * sin (m * θ) - sin ((m - 1) * θ) := by
    have h₁ : (m + 1) * θ = m * θ + θ := by ring
    have h₂ : (m - 1) * θ = m * θ - θ := by ring
    rw [h₁, h₂, sin_add, sin_sub]
    ring
  suffices ∀ n : ℕ, sin θ • A ^ n = sin (n * θ) • A - sin ((n - 1) * θ) • 1 ∧
      sin θ • A ^ (n + 1) = sin ((n + 1 : ℕ) * θ) • A - sin ((((n + 1 : ℕ) : ℝ) - 1) * θ) • 1 from
    (this n).1
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [pow_add_two_fin_two, hdet, htr, one_smul, smul_sub, smul_comm, ih.2, ih.1]
    have e₁ := hsin ((n + 1 : ℕ) : ℝ)
    have e₂ := hsin (n : ℝ)
    push_cast at e₁ e₂ ⊢
    -- Normalize the predecessor indices so the sine recurrence matches the casted goal.
    rw [show (n : ℝ) + 1 + 1 - 1 = n + 1 by ring, show (n : ℝ) + 1 - 1 = n by ring] at *
    rw [e₁, e₂]
    module

/-- A real `2 × 2` matrix of determinant one and trace `2 cos (π / k)`, with `2 ≤ k`, has `k`-th
power `-1`. Its image in `PSL(2, ℝ)` has order dividing `k`. -/
theorem pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div {A : Matrix (Fin 2) (Fin 2) ℝ} {k : ℕ}
    (hdet : A.det = 1) (hk : 2 ≤ k) (htr : A.trace = 2 * cos (π / k)) : A ^ k = -1 := by
  have hk₀ : (k : ℝ) ≠ 0 := by positivity
  have hk₁ : (1 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < sin (π / k) := sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self pi_pos hk₁)
  have h := sin_smul_pow_fin_two hdet htr k
  -- Normalize the two sine arguments before using `sin_pi` and `sin_pi_sub`.
  rw [show (k : ℝ) * (π / k) = π by field_simp, show ((k : ℝ) - 1) * (π / k) = π - π / k by
    field_simp, sin_pi, sin_pi_sub, zero_smul, zero_sub, ← smul_neg] at h
  exact smul_right_injective _ hs.ne' h

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
