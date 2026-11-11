/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.Data.Matrix.Block
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Topology.Algebra.Module.Matrix
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# The exponential of an upper block triangular matrix

The exponential of `[[A, B], [0, D]]` has diagonal blocks `exp A` and `exp D` and upper-right
block `∫ t in 0..1, exp ((1-t) • A) * B * exp (t • D)`. The formula holds over every complete
real normed algebra, with no commutation assumption on the blocks and with empty blocks allowed.
For block-diagonal matrices, exponentiation commutes with forming the blocks over any complete
rational normed coefficient algebra.

For a final one-dimensional block `D`, this describes the last column of the exponential as a
linear function of `B`, which is the off-diagonal step in constructing triangular logarithms.

## Main results

* `Matrix.toBlocks₁₁_exp_fromBlocks_zero₂₁`, `Matrix.toBlocks₂₂_exp_fromBlocks_zero₂₁`, and
  `Matrix.toBlocks₂₁_exp_fromBlocks_zero₂₁`: the diagonal and lower-left exponential blocks.
* `Matrix.toBlocks₁₂_exp_fromBlocks_zero₂₁`: the upper-right exponential block as an integral.
* `Matrix.exp_fromBlocks_diagonal`: the exponential of a block-diagonal matrix.
* `Matrix.exp_fromBlocks_zero₂₁`: the exponential of an upper two-block matrix, with the
  off-diagonal block given by its exponential-weight integral.

## References

* C. F. Van Loan, *Computing Integrals Involving the Matrix Exponential*, IEEE Transactions
  on Automatic Control 23(3) (1978), 395–404, Theorem 1, pp. 395–396,
  DOI: 10.1109/TAC.1978.1101743.
-/

public section

noncomputable section

attribute [local instance] TauCeti.normedAlgebraRatOfReal

open NormedSpace

namespace Matrix

open scoped Matrix.Norms.Operator

section Topological

variable {R m n : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] [Algebra ℚ R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The lower-left block of the exponential of an upper two-block matrix is zero. -/
@[simp] theorem toBlocks₂₁_exp_fromBlocks_zero₂₁
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (exp (fromBlocks A B 0 D)).toBlocks₂₁ = 0 := by
  ext i j
  simpa only [toBlocks₂₁, of_apply, Matrix.zero_apply] using
    (upper_two_blockTriangular A B D (show (0 : ℕ) < 1 by decide)).exp
      (i := Sum.inr i) (j := Sum.inl j) (by simp)

end Topological

variable {R m n : Type*} [NormedRing R] [CompleteSpace R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Rational

variable [NormedAlgebra ℚ R]

/-- The upper-left block of the exponential of an upper two-block matrix equals `exp A`. -/
@[simp] theorem toBlocks₁₁_exp_fromBlocks_zero₂₁
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (exp (fromBlocks A B 0 D)).toBlocks₁₁ = exp A := by
  ext i j
  simp only [toBlocks₁₁, of_apply]
  apply exp_apply_eq_of_forall_pow_apply_eq
  intro k
  rw [fromBlocks_zero₂₁_pow, fromBlocks_apply₁₁]

/-- The lower-right block of the exponential of an upper two-block matrix equals `exp D`. -/
@[simp] theorem toBlocks₂₂_exp_fromBlocks_zero₂₁
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (exp (fromBlocks A B 0 D)).toBlocks₂₂ = exp D := by
  ext i j
  simp only [toBlocks₂₂, of_apply]
  apply exp_apply_eq_of_forall_pow_apply_eq
  intro k
  rw [fromBlocks_zero₂₁_pow, fromBlocks_apply₂₂]

private theorem exp_fromBlocks_zero₂₁_eq_fromBlocks
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    exp (fromBlocks A B 0 D) =
      fromBlocks (exp A) (exp (fromBlocks A B 0 D)).toBlocks₁₂ 0 (exp D) := by
  simpa only [toBlocks₁₁_exp_fromBlocks_zero₂₁, toBlocks₂₁_exp_fromBlocks_zero₂₁,
    toBlocks₂₂_exp_fromBlocks_zero₂₁] using
    (fromBlocks_toBlocks (exp (fromBlocks A B 0 D))).symm

/-- The exponential of a two-block diagonal matrix is block diagonal. A complete normed
rational-algebra structure on the coefficient ring suffices. -/
@[simp] theorem exp_fromBlocks_diagonal (A : Matrix m m R) (D : Matrix n n R) :
    exp (fromBlocks A 0 0 D) = fromBlocks (exp A) 0 0 (exp D) := by
  rw [exp_fromBlocks_zero₂₁_eq_fromBlocks]
  congr 1
  ext i j
  have h := exp_series_hasSum_exp_apply (fromBlocks A 0 0 D) (Sum.inl i) (Sum.inr j)
  simp only [fromBlocks_diagonal_pow, fromBlocks_apply₁₂, Matrix.zero_apply, smul_zero] at h
  simpa only [toBlocks₁₂, of_apply, Matrix.zero_apply] using h.unique hasSum_zero

end Rational

section Real

variable [NormedAlgebra ℝ R]

/-- The exponential of an upper two-block matrix. The off-diagonal block is an integral of the
left and right diagonal exponential weights, with no commutation hypotheses. -/
theorem exp_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    exp (fromBlocks A B 0 D) =
      fromBlocks (exp A)
        (∫ t in (0 : ℝ)..1, exp ((1 - t) • A) * B * exp (t • D)) 0 (exp D) := by
  let E := fromBlocks₁₂CLM ℝ (R := R) (m := m) (n := n) (l := m) (o := n)
  let x := fromBlocks A (0 : Matrix m n R) 0 D
  let h := fromBlocks (0 : Matrix m m R) B 0 (0 : Matrix n n R)
  have hsum : x + h = fromBlocks A B 0 D := by simp [x, h, fromBlocks_add]
  have hm (t : ℝ) : exp ((1 - t) • (x + h)) * h * exp (t • x) =
      E (exp ((1 - t) • A) * B * exp (t • D)) := by
    simp only [hsum, x, h, fromBlocks_smul, smul_zero]
    rw [exp_fromBlocks_zero₂₁_eq_fromBlocks, exp_fromBlocks_diagonal]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      E, fromBlocks₁₂CLM_apply]
  -- Select the norm-induced extended norm: the rectangular matrix default can follow
  -- a different instance path from the operator norm used by the integral.
  let _ : ENormedAddMonoid (Matrix m n R) := NormedAddGroup.toENormedAddMonoid
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp ((1 - t) • A) * B * exp (t • D)) MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hd : exp (x + h) - exp x =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + h)) * h * exp (t • x) :=
    TauCeti.exp_add_sub_exp_eq_integral x h
  simp_rw [hm] at hd
  have hcomm : (∫ t in (0 : ℝ)..1, E (exp ((1 - t) • A) * B * exp (t • D))) =
      E (∫ t in (0 : ℝ)..1, exp ((1 - t) • A) * B * exp (t • D)) :=
    E.intervalIntegral_comp_comm hint
  rw [hcomm] at hd
  rw [hsum] at hd
  simp only [x, exp_fromBlocks_diagonal] at hd
  have heq := sub_eq_iff_eq_add.mp hd
  simpa only [E, fromBlocks₁₂CLM_apply, fromBlocks_add, zero_add, add_zero] using heq

/-- The upper-right block of the exponential is the integral of its diagonal exponential weights
acting on the original upper-right block. -/
@[simp] theorem toBlocks₁₂_exp_fromBlocks_zero₂₁
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (exp (fromBlocks A B 0 D)).toBlocks₁₂ =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • A) * B * exp (t • D) := by
  rw [exp_fromBlocks_zero₂₁, toBlocks_fromBlocks₁₂]

end Real

end Matrix
