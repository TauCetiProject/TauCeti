/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matrix trace bounds and their equality case

For a symmetric matrix, trace Cauchy–Schwarz bounds the square of the trace by the dimension
times the trace of the square. Completing the square around a scalar matrix characterizes the
equality case in the Cauchy–Schwarz bound for the trace. This equality criterion needs no
symmetry assumption and is used for the Hessian in sharp eigenvalue estimates.

Formalization references for the symmetric bounds:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of squared entries after subtracting a scalar matrix, expanded using the trace. -/
theorem sum_sq_sub_scalar (A : Matrix ι ι R) (c : R) :
    (∑ i, ∑ j, (A i j - (scalar ι c) i j) ^ 2) =
      (∑ i, ∑ j, A i j ^ 2) - 2 * c * A.trace + Fintype.card ι * c ^ 2 := by
  have hrow (i : ι) : (∑ j, (A i j - (scalar ι c) i j) ^ 2) =
      (∑ j, A i j ^ 2) - 2 * c * A i i + c ^ 2 := by
    calc
      _ = ∑ j, (A i j ^ 2 + if i = j then -2 * c * A i i + c ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · subst j
          simp only [scalar_apply, diagonal_apply_eq, ↓reduceIte]
          ring
        · simp only [scalar_apply, diagonal_apply, h, ↓reduceIte, sub_zero, add_zero]
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        ring
  simp_rw [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, trace, diag_apply]

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- A matrix with trace `card ι * c` and squared entry sum at most `card ι * c²`
is the scalar matrix `c`. The empty index type is allowed. -/
theorem eq_scalar_of_trace_eq_of_sum_sq_le (A : Matrix ι ι R) (c : R)
    (htrace : A.trace = Fintype.card ι * c)
    (hsq : (∑ i, ∑ j, A i j ^ 2) ≤ Fintype.card ι * c ^ 2) :
    A = scalar ι c := by
  have hz : (∑ i, ∑ j, (A i j - (scalar ι c) i j) ^ 2) = 0 := by
    have hnonneg : 0 ≤ ∑ i, ∑ j, (A i j - (scalar ι c) i j) ^ 2 := by positivity
    rw [sum_sq_sub_scalar, htrace] at *
    nlinarith
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).1 hz
  ext i j
  exact sub_eq_zero.mp ((Finset.sum_sq_eq_zero_iff _ _).1
    (hentry i (Finset.mem_univ i)) j (Finset.mem_univ j))

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The trace of the square of a symmetric matrix controls its diagonal
square sum. -/
theorem sum_sq_diag_le_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι 𝕜} (hS : S.IsSymm) :
    (∑ i, S i i ^ 2) ≤ (S * S).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro i _
  have hs : ∀ j, S i j * S j i = S i j ^ 2 := by
    intro j
    rw [hS.apply i j, pow_two]
  simp only [hs]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (S i j)) (Finset.mem_univ i)

/-- Cauchy--Schwarz for the trace of a symmetric matrix, including the
zero-dimensional case. -/
theorem sq_trace_le_card_mul_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι 𝕜} (hS : S.IsSymm) :
    S.trace ^ 2 ≤ (Fintype.card ι : 𝕜) * (S * S).trace := by
  have hdiag : S.trace ^ 2 ≤ (Fintype.card ι : 𝕜) * ∑ i, S i i ^ 2 := by
    simpa only [Matrix.trace, Matrix.diag, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ S i i))
  exact hdiag.trans (mul_le_mul_of_nonneg_left
    (sum_sq_diag_le_trace_mul_self hS) (Nat.cast_nonneg _))

end Matrix
