/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.Matrix.Order

/-!
# The normalized trace and 2-norm on matrix algebras

On the matrix C⋆-algebra `CStarMatrix n n ℂ` over a finite index type `n` with `k` elements, with
its operator norm, this file defines the normalized trace `tr_k(x) = k⁻¹ Tr(x)` and the normalized
2-norm `‖x‖₂ = tr_k(x⋆x)^{1/2}`, and proves the comparison inequalities between `‖·‖₂` and the
operator norm `‖·‖` that are used to measure multiplicativity defects of completely positive maps
into matrix algebras. The matrix algebra `M_k` is the case `n = Fin k`.

The 2-norm is `k^{-1/2}` times the Frobenius norm, and `tr_k(x⋆y) = k⁻¹⟪x, y⟫_F` for the complex
Frobenius inner product `Matrix.frobeniusInnerProductSpace`, so the norm axioms and the
Cauchy–Schwarz inequality come from that inner product space. The comparisons with the operator
norm come from the C⋆-order: `y⋆(x⋆x)y ≤ ‖x‖² y⋆y` and the trace is monotone.

## Main declarations

* `CStarMatrix.normalizedTrace`: the normalized trace `tr_k`, with `tr_k(1) = 1` for `k ≠ 0`,
  `tr_k(xy) = tr_k(yx)` and monotonicity for the C⋆-order; `CStarMatrix.normalizedTrace_matrixUnit`
  evaluates it on matrix units.
* `CStarMatrix.normalizedTraceMap`: `tr_k` as a positive continuous linear functional, of norm
  at most `1` (`CStarMatrix.norm_normalizedTraceMap_le`), with equality for `k ≠ 0`, and
  invariant under reindexing (`CStarMatrix.normalizedTraceMap_comp_reindexₐ`).
* `CStarMatrix.normalizedTwoNorm`: the normalized 2-norm `‖x‖₂`.
* `CStarMatrix.normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm`: `‖x‖₂ = k^{-1/2}‖x‖_F`.
* `CStarMatrix.normalizedTwoNorm_matrixUnit`: `‖e_ij‖₂ = k^{-1/2}`.
* `CStarMatrix.normalizedTwoNormAddGroupNorm`: `‖·‖₂` as an additive group norm; its complex
  homogeneity is `CStarMatrix.normalizedTwoNorm_smul`.
* `CStarMatrix.norm_normalizedTrace_star_mul_le`: Cauchy–Schwarz `|tr_k(x⋆y)| ≤ ‖x‖₂‖y‖₂`, and
  `CStarMatrix.norm_normalizedTrace_le_normalizedTwoNorm`: `|tr_k(x)| ≤ ‖x‖₂`.
* `CStarMatrix.normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm`,
  `CStarMatrix.normalizedTwoNorm_mul_le_normalizedTwoNorm_mul_norm`,
  `CStarMatrix.normalizedTwoNorm_le_norm`, `CStarMatrix.normalizedTwoNorm_star`:
  `‖xy‖₂ ≤ ‖x‖‖y‖₂`, `‖xy‖₂ ≤ ‖x‖₂‖y‖`, `‖x‖₂ ≤ ‖x‖` and `‖x⋆‖₂ = ‖x‖₂`.
* `CStarMatrix.normalizedTrace_conj_of_mul_eq_one`,
  `CStarMatrix.normalizedTwoNorm_mul_left_of_star_mul_self`,
  `CStarMatrix.normalizedTwoNorm_mul_right_of_mul_star_self`: invariance of `tr_k` under
  conjugation and of `‖·‖₂` under multiplication by isometries and coisometries.
* `CStarMatrix.normalizedTwoNorm_sub_mul_mul_le`: `‖x - cxd‖₂ ≤ ‖x‖(‖c - 1‖₂ + ‖c‖‖d - 1‖₂)`, and
  `CStarMatrix.normalizedTwoNorm_sub_mul_mul_le_of_norm_le_one`: `‖x - cxc‖₂ ≤ 2‖x‖‖c - 1‖₂` for a
  contraction `c`.
* `CStarMatrix.normalizedTrace_reindexₐ`, `CStarMatrix.normalizedTwoNorm_reindexₐ`: `tr_k` and
  `‖·‖₂` do not depend on the labelling of the index type, so the statements below over `n ⊕ m`
  and `n × m` give those over `Fin (k + l)` and `Fin (k * l)`.
* `CStarMatrix.normalizedTrace_fromBlocks`, `CStarMatrix.normalizedTwoNorm_fromBlocks_sq`: block
  additivity `tr_{k+l}(x ⊕ y) = (k tr_k(x) + l tr_l(y))/(k + l)`, and the same for `‖·‖₂²`; the
  `simp` forms `CStarMatrix.normalizedTrace_ofMatrix_fromBlocks` and
  `CStarMatrix.normalizedTwoNorm_ofMatrix_fromBlocks_sq` take `Matrix` blocks.
* `CStarMatrix.normalizedTrace_kronecker`, `CStarMatrix.normalizedTwoNorm_kronecker`: tensor
  multiplicativity `tr_{kl}(x ⊗ y) = tr_k(x) tr_l(y)` and `‖x ⊗ y‖₂ = ‖x‖₂‖y‖₂` for the Kronecker
  product; the `simp` forms `CStarMatrix.normalizedTrace_ofMatrix_kronecker` and
  `CStarMatrix.normalizedTwoNorm_ofMatrix_kronecker` take `Matrix` arguments.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2 (numbering cited), Chapter 2
  and the proof of Lemma 2.7.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math. 185
  (2017), §1.
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder InnerProductSpace Kronecker Matrix.Norms.Frobenius

namespace CStarMatrix

variable {n : Type*} [Fintype n]

/-- The normalized trace `tr_k(x) = k⁻¹ Σᵢ xᵢᵢ` on `CStarMatrix n n ℂ`, where `k` is the
cardinality of `n`: the unique tracial state for `k ≥ 1`, and `0` for `k = 0`. In `M_2`,
`tr_2(1) = 1` and `tr_2(e₁₁) = 1/2`. -/
def normalizedTrace (x : CStarMatrix n n ℂ) : ℂ :=
  (Fintype.card n : ℂ)⁻¹ * (ofMatrix.symm x).trace

/-- Unfolding lemma for `normalizedTrace`. -/
theorem normalizedTrace_def (x : CStarMatrix n n ℂ) :
    normalizedTrace x = (Fintype.card n : ℂ)⁻¹ * (ofMatrix.symm x).trace :=
  (rfl)

/-- The normalized trace is the averaged sum of the diagonal entries. -/
theorem normalizedTrace_eq_sum (x : CStarMatrix n n ℂ) :
    normalizedTrace x = (Fintype.card n : ℂ)⁻¹ * ∑ i, x i i := by
  simp [normalizedTrace_def, Matrix.trace]

/-- The normalized trace of `0` is `0`. -/
@[simp]
theorem normalizedTrace_zero : normalizedTrace (0 : CStarMatrix n n ℂ) = 0 := by
  simp [normalizedTrace_def]

/-- The normalized trace is additive. -/
@[simp]
theorem normalizedTrace_add (x y : CStarMatrix n n ℂ) :
    normalizedTrace (x + y) = normalizedTrace x + normalizedTrace y := by
  simp [normalizedTrace_def, mul_add]

/-- The normalized trace commutes with negation. -/
@[simp]
theorem normalizedTrace_neg (x : CStarMatrix n n ℂ) :
    normalizedTrace (-x) = -normalizedTrace x := by
  simp [normalizedTrace_def]

/-- The normalized trace commutes with subtraction. -/
@[simp]
theorem normalizedTrace_sub (x y : CStarMatrix n n ℂ) :
    normalizedTrace (x - y) = normalizedTrace x - normalizedTrace y := by
  simp [normalizedTrace_def, mul_sub]

/-- The normalized trace is complex-homogeneous. -/
@[simp]
theorem normalizedTrace_smul (c : ℂ) (x : CStarMatrix n n ℂ) :
    normalizedTrace (c • x) = c * normalizedTrace x := by
  simp [normalizedTrace_def, mul_left_comm]

/-- The normalized trace of a finite sum is the sum of the normalized traces. -/
@[simp]
theorem normalizedTrace_sum {ι : Type*} (s : Finset ι) (x : ι → CStarMatrix n n ℂ) :
    normalizedTrace (∑ i ∈ s, x i) = ∑ i ∈ s, normalizedTrace (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- The normalized trace of the identity is `1` for a nonempty index type. -/
@[simp]
theorem normalizedTrace_one [DecidableEq n] [Nonempty n] :
    normalizedTrace (1 : CStarMatrix n n ℂ) = 1 := by
  rw [normalizedTrace_def, ofMatrix_symm_one, Matrix.trace_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The normalized trace of the matrix unit `e_ij` is `1/k` if `i = j` and `0` otherwise. -/
@[simp]
theorem normalizedTrace_matrixUnit [DecidableEq n] (i j : n) :
    normalizedTrace (matrixUnit i j) = if i = j then (Fintype.card n : ℂ)⁻¹ else 0 := by
  split_ifs with h
  · simp [normalizedTrace_eq_sum, matrixUnit_apply, h]
  · simp [normalizedTrace_eq_sum, matrixUnit_apply, Ne.symm h]

/-- On matrices with an empty index type the normalized trace vanishes. -/
@[simp]
theorem normalizedTrace_of_isEmpty [IsEmpty n] (x : CStarMatrix n n ℂ) :
    normalizedTrace x = 0 := by
  simp [normalizedTrace_eq_sum]

/-- The normalized trace is tracial. -/
theorem normalizedTrace_mul_comm (x y : CStarMatrix n n ℂ) :
    normalizedTrace (x * y) = normalizedTrace (y * x) := by
  rw [normalizedTrace_def, normalizedTrace_def, ofMatrix_symm_mul, ofMatrix_symm_mul,
    Matrix.trace_mul_comm]

/-- The normalized trace of the adjoint is the conjugate of the normalized trace. -/
@[simp]
theorem normalizedTrace_star (x : CStarMatrix n n ℂ) :
    normalizedTrace (star x) = star (normalizedTrace x) := by
  simp [normalizedTrace_def, Matrix.trace_conjTranspose]

/-- The normalized trace is invariant under conjugation `x ↦ uxv` by a left-invertible pair
`vu = 1`. -/
theorem normalizedTrace_conj_of_mul_eq_one [DecidableEq n] {u v : CStarMatrix n n ℂ}
    (h : v * u = 1) (x : CStarMatrix n n ℂ) : normalizedTrace (u * x * v) = normalizedTrace x := by
  rw [normalizedTrace_mul_comm, ← mul_assoc, h, one_mul]

/-- The normalized trace is invariant under conjugation by an invertible matrix. -/
theorem normalizedTrace_units_conj [DecidableEq n] (u : (CStarMatrix n n ℂ)ˣ)
    (x : CStarMatrix n n ℂ) :
    normalizedTrace ((u : CStarMatrix n n ℂ) * x * (↑u⁻¹ : CStarMatrix n n ℂ)) =
      normalizedTrace x :=
  normalizedTrace_conj_of_mul_eq_one u.inv_mul x

/-- The normalized trace is invariant under unitary conjugation. -/
theorem normalizedTrace_unitary_conj [DecidableEq n] {u : CStarMatrix n n ℂ}
    (hu : u ∈ unitary (CStarMatrix n n ℂ)) (x : CStarMatrix n n ℂ) :
    normalizedTrace (u * x * star u) = normalizedTrace x :=
  normalizedTrace_conj_of_mul_eq_one (Unitary.star_mul_self_of_mem hu) x

/-- The normalized trace of a positive matrix is nonnegative. -/
theorem normalizedTrace_nonneg {x : CStarMatrix n n ℂ} (hx : 0 ≤ x) :
    0 ≤ normalizedTrace x := by
  rw [normalizedTrace_def]
  exact mul_nonneg (by simp) (nonneg_iff_posSemidef.mp hx).trace_nonneg

/-- The normalized trace is monotone for the C⋆-order. -/
theorem normalizedTrace_mono {x y : CStarMatrix n n ℂ} (h : x ≤ y) :
    normalizedTrace x ≤ normalizedTrace y := by
  have := normalizedTrace_nonneg (sub_nonneg.mpr h)
  rwa [normalizedTrace_sub, sub_nonneg] at this

/-- `tr_k(x⋆y) = k⁻¹⟪x, y⟫_F` for the complex Frobenius inner product. -/
theorem normalizedTrace_star_mul_eq_inv_mul_frobenius_inner (x y : CStarMatrix n n ℂ) :
    normalizedTrace (star x * y) =
      (Fintype.card n : ℂ)⁻¹ * ⟪ofMatrix.symm x, ofMatrix.symm y⟫_ℂ := by
  rw [normalizedTrace_def, frobenius_inner_eq_trace_conjTranspose_mul, ofMatrix_symm_mul,
    ofMatrix_symm_star]

/-- The normalized 2-norm `‖x‖₂ = tr_k(x⋆x)^{1/2}` on `CStarMatrix n n ℂ`, `k^{-1/2}` times the
Frobenius norm. In `M_2`, `‖e₁₁‖₂ = 2^{-1/2}`. -/
def normalizedTwoNorm (x : CStarMatrix n n ℂ) : ℝ :=
  Real.sqrt (normalizedTrace (star x * x)).re

/-- Unfolding lemma for `normalizedTwoNorm`. -/
theorem normalizedTwoNorm_def (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm x = Real.sqrt (normalizedTrace (star x * x)).re :=
  (rfl)

/-- The normalized 2-norm is `k^{-1/2}` times the Frobenius norm. -/
theorem normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm x = (Real.sqrt (Fintype.card n))⁻¹ * ‖ofMatrix.symm x‖ := by
  have h : normalizedTrace (star x * x) =
      (((Fintype.card n : ℝ)⁻¹ * ‖ofMatrix.symm x‖ ^ 2 : ℝ) : ℂ) := by
    rw [normalizedTrace_star_mul_eq_inv_mul_frobenius_inner, inner_self_eq_norm_sq_to_K]
    simp
  rw [normalizedTwoNorm_def, h, Complex.ofReal_re, Real.sqrt_mul (by positivity), Real.sqrt_inv,
    Real.sqrt_sq (norm_nonneg _)]

/-- The normalized 2-norm is nonnegative. -/
@[simp, bound]
theorem normalizedTwoNorm_nonneg (x : CStarMatrix n n ℂ) : 0 ≤ normalizedTwoNorm x :=
  Real.sqrt_nonneg _

/-- The normalized 2-norm is its own absolute value. -/
@[simp]
theorem abs_normalizedTwoNorm (x : CStarMatrix n n ℂ) :
    |normalizedTwoNorm x| = normalizedTwoNorm x :=
  abs_of_nonneg (normalizedTwoNorm_nonneg x)

/-- `tr_k(x⋆x) = ‖x‖₂²`. -/
theorem normalizedTrace_star_mul_self (x : CStarMatrix n n ℂ) :
    normalizedTrace (star x * x) = ((normalizedTwoNorm x ^ 2 : ℝ) : ℂ) := by
  rw [normalizedTrace_star_mul_eq_inv_mul_frobenius_inner, inner_self_eq_norm_sq_to_K]
  simp [normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_pow]

/-- `‖x‖₂² = Re tr_k(x⋆x)`. -/
theorem normalizedTwoNorm_sq (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm x ^ 2 = (normalizedTrace (star x * x)).re := by
  rw [normalizedTrace_star_mul_self, Complex.ofReal_re]

/-- `‖0‖₂ = 0`. -/
@[simp]
theorem normalizedTwoNorm_zero : normalizedTwoNorm (0 : CStarMatrix n n ℂ) = 0 := by
  simp [normalizedTwoNorm_def]

/-- On matrices with an empty index type the normalized 2-norm vanishes. -/
@[simp]
theorem normalizedTwoNorm_of_isEmpty [IsEmpty n] (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm x = 0 := by
  simp [normalizedTwoNorm_def]

/-- The normalized 2-norm is definite. -/
@[simp]
theorem normalizedTwoNorm_eq_zero_iff {x : CStarMatrix n n ℂ} :
    normalizedTwoNorm x = 0 ↔ x = 0 := by
  cases isEmpty_or_nonempty n
  · exact iff_of_true (normalizedTwoNorm_of_isEmpty x)
      (CStarMatrix.ext fun i _ ↦ isEmptyElim i)
  · have : (Real.sqrt (Fintype.card n))⁻¹ ≠ 0 := by positivity
    rw [normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_eq_zero, or_iff_right this,
      norm_eq_zero, ← ofMatrix_symm_zero, ofMatrix.symm.injective.eq_iff]

/-- The normalized trace is faithful: `tr_k(x⋆x) = 0` only for `x = 0`. -/
theorem normalizedTrace_star_mul_self_eq_zero_iff {x : CStarMatrix n n ℂ} :
    normalizedTrace (star x * x) = 0 ↔ x = 0 := by
  simp [normalizedTrace_star_mul_self]

/-- The triangle inequality for the normalized 2-norm. -/
theorem normalizedTwoNorm_add_le (x y : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x + y) ≤ normalizedTwoNorm x + normalizedTwoNorm y := by
  simp only [normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm, ofMatrix_symm_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- The normalized 2-norm is absolutely homogeneous. -/
theorem normalizedTwoNorm_smul (c : ℂ) (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (c • x) = ‖c‖ * normalizedTwoNorm x := by
  rw [normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm,
    normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm, ofMatrix_symm_smul, norm_smul,
    mul_left_comm]

/-- `‖-x‖₂ = ‖x‖₂`. -/
@[simp]
theorem normalizedTwoNorm_neg (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (-x) = normalizedTwoNorm x := by
  simpa using normalizedTwoNorm_smul (-1) x

/-- `‖x - y‖₂ = ‖y - x‖₂`. -/
theorem normalizedTwoNorm_sub_comm (x y : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x - y) = normalizedTwoNorm (y - x) := by
  rw [← neg_sub, normalizedTwoNorm_neg]

variable (n) in
/-- The normalized 2-norm as an additive group norm on `CStarMatrix n n ℂ`. It is not registered
as an instance, since `CStarMatrix n n ℂ` carries its operator norm. -/
def normalizedTwoNormAddGroupNorm : AddGroupNorm (CStarMatrix n n ℂ) where
  toFun := normalizedTwoNorm
  map_zero' := normalizedTwoNorm_zero
  add_le' := normalizedTwoNorm_add_le
  neg' := normalizedTwoNorm_neg
  eq_zero_of_map_eq_zero' _ := normalizedTwoNorm_eq_zero_iff.mp

/-- `normalizedTwoNormAddGroupNorm n` evaluates to the normalized 2-norm. -/
@[simp]
theorem normalizedTwoNormAddGroupNorm_apply (x : CStarMatrix n n ℂ) :
    normalizedTwoNormAddGroupNorm n x = normalizedTwoNorm x :=
  (rfl)

/-- The triangle inequality for differences in the normalized 2-norm. -/
theorem normalizedTwoNorm_sub_le (x y : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x - y) ≤ normalizedTwoNorm x + normalizedTwoNorm y := by
  simpa using map_sub_le_add (normalizedTwoNormAddGroupNorm n) x y

/-- The reverse triangle inequality for the normalized 2-norm. -/
theorem abs_normalizedTwoNorm_sub_normalizedTwoNorm_le (x y : CStarMatrix n n ℂ) :
    |normalizedTwoNorm x - normalizedTwoNorm y| ≤ normalizedTwoNorm (x - y) := by
  simpa using abs_sub_map_le_sub (normalizedTwoNormAddGroupNorm n) x y

/-- The triangle inequality for finite sums in the normalized 2-norm. -/
theorem normalizedTwoNorm_sum_le {ι : Type*} (s : Finset ι) (x : ι → CStarMatrix n n ℂ) :
    normalizedTwoNorm (∑ i ∈ s, x i) ≤ ∑ i ∈ s, normalizedTwoNorm (x i) :=
  Finset.le_sum_of_subadditive _ normalizedTwoNorm_zero.le normalizedTwoNorm_add_le s x

/-- The Cauchy–Schwarz inequality `|tr_k(x⋆y)| ≤ ‖x‖₂‖y‖₂`. -/
theorem norm_normalizedTrace_star_mul_le (x y : CStarMatrix n n ℂ) :
    ‖normalizedTrace (star x * y)‖ ≤ normalizedTwoNorm x * normalizedTwoNorm y := by
  rw [normalizedTrace_star_mul_eq_inv_mul_frobenius_inner,
    normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm,
    normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_mul_mul_comm, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)

/-- `‖1‖₂ = 1` for a nonempty index type. -/
@[simp]
theorem normalizedTwoNorm_one [DecidableEq n] [Nonempty n] :
    normalizedTwoNorm (1 : CStarMatrix n n ℂ) = 1 := by
  simp [normalizedTwoNorm_def]

/-- `‖1‖₂ ≤ 1` for every finite index type; see `normalizedTwoNorm_one` for the equality when
the index type is nonempty. -/
theorem normalizedTwoNorm_one_le [DecidableEq n] : normalizedTwoNorm (1 : CStarMatrix n n ℂ) ≤ 1 :=
  by cases isEmpty_or_nonempty n <;> simp

/-- `‖e_ij‖₂ = k^{-1/2}`. -/
@[simp]
theorem normalizedTwoNorm_matrixUnit [DecidableEq n] (i j : n) :
    normalizedTwoNorm (matrixUnit i j) = (√(Fintype.card n))⁻¹ := by
  simp [normalizedTwoNorm_def, Real.sqrt_inv]

/-- `|tr_k(x)| ≤ ‖x‖₂`, Cauchy–Schwarz against the identity. -/
theorem norm_normalizedTrace_le_normalizedTwoNorm (x : CStarMatrix n n ℂ) :
    ‖normalizedTrace x‖ ≤ normalizedTwoNorm x := by
  classical
  simpa using (norm_normalizedTrace_star_mul_le 1 x).trans
    (mul_le_of_le_one_left (normalizedTwoNorm_nonneg x) normalizedTwoNorm_one_le)

/-- The normalized 2-norm is invariant under the adjoint. -/
@[simp]
theorem normalizedTwoNorm_star (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (star x) = normalizedTwoNorm x := by
  rw [normalizedTwoNorm_def, normalizedTwoNorm_def, star_star, normalizedTrace_mul_comm]

/-- `‖xy‖₂ ≤ ‖x‖‖y‖₂`. -/
theorem normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm (x y : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x * y) ≤ ‖x‖ * normalizedTwoNorm y := by
  have h : star (x * y) * (x * y) ≤ ((‖x‖ ^ 2 : ℝ) : ℂ) • (star y * y) := by
    have h' := CStarAlgebra.star_left_conjugate_le_norm_smul y (star x * x)
    rw [CStarRing.norm_star_mul_self (x := x), ← sq, ← Complex.coe_smul] at h'
    simpa only [star_mul, mul_assoc] using h'
  have h2 := Complex.re_le_re (normalizedTrace_mono h)
  rw [normalizedTrace_smul, Complex.re_ofReal_mul, ← normalizedTwoNorm_sq,
    ← normalizedTwoNorm_sq, ← mul_pow] at h2
  exact pow_le_pow_iff_left₀ (normalizedTwoNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (normalizedTwoNorm_nonneg _)) two_ne_zero |>.mp h2

/-- `‖xy‖₂ ≤ ‖x‖₂‖y‖`. -/
theorem normalizedTwoNorm_mul_le_normalizedTwoNorm_mul_norm (x y : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x * y) ≤ normalizedTwoNorm x * ‖y‖ := by
  rw [← normalizedTwoNorm_star, star_mul, mul_comm, ← norm_star y, ← normalizedTwoNorm_star x]
  exact normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm _ _

/-- `‖x‖₂ ≤ ‖x‖`. -/
theorem normalizedTwoNorm_le_norm (x : CStarMatrix n n ℂ) : normalizedTwoNorm x ≤ ‖x‖ := by
  classical
  simpa using (normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm x 1).trans
    (mul_le_of_le_one_right (norm_nonneg x) normalizedTwoNorm_one_le)

/-- The normalized 2-norm is `1`-Lipschitz for the operator norm. -/
theorem lipschitzWith_normalizedTwoNorm :
    LipschitzWith 1 (normalizedTwoNorm : CStarMatrix n n ℂ → ℝ) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact (abs_normalizedTwoNorm_sub_normalizedTwoNorm_le x y).trans (normalizedTwoNorm_le_norm _)

/-- The normalized 2-norm is continuous for the operator norm. -/
theorem continuous_normalizedTwoNorm : Continuous (normalizedTwoNorm : CStarMatrix n n ℂ → ℝ) :=
  lipschitzWith_normalizedTwoNorm.continuous

/-- `|tr_k(x)| ≤ ‖x‖`. -/
theorem norm_normalizedTrace_le_norm (x : CStarMatrix n n ℂ) : ‖normalizedTrace x‖ ≤ ‖x‖ :=
  (norm_normalizedTrace_le_normalizedTwoNorm x).trans (normalizedTwoNorm_le_norm x)

/-- The normalized trace is continuous for the operator norm. -/
theorem continuous_normalizedTrace : Continuous (normalizedTrace : CStarMatrix n n ℂ → ℂ) :=
  AddMonoidHomClass.continuous_of_bound
    (AddMonoidHom.mk' normalizedTrace normalizedTrace_add) 1 fun x ↦ by
      simpa using norm_normalizedTrace_le_norm x

variable (n) in
/-- The normalized trace as a positive continuous linear functional on `CStarMatrix n n ℂ`. -/
def normalizedTraceMap : CStarMatrix n n ℂ →P[ℂ] ℂ where
  toFun := normalizedTrace
  map_add' := normalizedTrace_add
  map_smul' := normalizedTrace_smul
  monotone' _ _ := normalizedTrace_mono
  cont := continuous_normalizedTrace

/-- `normalizedTraceMap n` evaluates to the normalized trace. -/
@[simp]
theorem normalizedTraceMap_apply (x : CStarMatrix n n ℂ) :
    normalizedTraceMap n x = normalizedTrace x :=
  (rfl)

variable (n) in
/-- The normalized trace has operator norm at most `1`. -/
theorem norm_normalizedTraceMap_le : ‖(normalizedTraceMap n).toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa using norm_normalizedTrace_le_norm x

variable (n) in
/-- The normalized trace has operator norm `1` for a nonempty index type. -/
theorem norm_normalizedTraceMap [Nonempty n] :
    ‖(normalizedTraceMap n).toContinuousLinearMap‖ = 1 := by
  classical
  refine le_antisymm (norm_normalizedTraceMap_le n) ?_
  simpa [CStarRing.norm_one] using (normalizedTraceMap n).toContinuousLinearMap.le_opNorm 1

/-- Left multiplication by an isometry `u⋆u = 1` preserves the normalized 2-norm. -/
theorem normalizedTwoNorm_mul_left_of_star_mul_self [DecidableEq n] {u : CStarMatrix n n ℂ}
    (hu : star u * u = 1) (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (u * x) = normalizedTwoNorm x := by
  rw [normalizedTwoNorm_def, normalizedTwoNorm_def, star_mul, ← mul_assoc, mul_assoc (star x),
    hu, mul_one]

/-- Right multiplication by a coisometry `uu⋆ = 1` preserves the normalized 2-norm. -/
theorem normalizedTwoNorm_mul_right_of_mul_star_self [DecidableEq n] {u : CStarMatrix n n ℂ}
    (hu : u * star u = 1) (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x * u) = normalizedTwoNorm x := by
  rw [normalizedTwoNorm_def, normalizedTwoNorm_def, star_mul, ← mul_assoc, mul_assoc (star u),
    normalizedTrace_conj_of_mul_eq_one hu]

/-- Conjugation `x ↦ uxu⋆` by an isometry `u⋆u = 1` preserves the normalized 2-norm. -/
theorem normalizedTwoNorm_conj_of_star_mul_self [DecidableEq n] {u : CStarMatrix n n ℂ}
    (hu : star u * u = 1) (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (u * x * star u) = normalizedTwoNorm x := by
  rw [normalizedTwoNorm_mul_right_of_mul_star_self (by rwa [star_star]),
    normalizedTwoNorm_mul_left_of_star_mul_self hu]

/-- The normalized 2-norm is invariant under unitary conjugation. -/
theorem normalizedTwoNorm_unitary_conj [DecidableEq n] {u : CStarMatrix n n ℂ}
    (hu : u ∈ unitary (CStarMatrix n n ℂ)) (x : CStarMatrix n n ℂ) :
    normalizedTwoNorm (u * x * star u) = normalizedTwoNorm x :=
  normalizedTwoNorm_conj_of_star_mul_self (Unitary.star_mul_self_of_mem hu) x

/-- `‖x - cxd‖₂ ≤ ‖x‖(‖c - 1‖₂ + ‖c‖‖d - 1‖₂)`: the estimate behind Brown (2006), proof of
Lemma 2.7. -/
theorem normalizedTwoNorm_sub_mul_mul_le [DecidableEq n] (x c d : CStarMatrix n n ℂ) :
    normalizedTwoNorm (x - c * x * d) ≤
      ‖x‖ * (normalizedTwoNorm (c - 1) + ‖c‖ * normalizedTwoNorm (d - 1)) := by
  have hdecomp : x - c * x * d = (1 - c) * x + c * (x * (1 - d)) := by noncomm_ring
  have h1 : normalizedTwoNorm ((1 - c) * x) ≤ ‖x‖ * normalizedTwoNorm (c - 1) := by
    rw [mul_comm, normalizedTwoNorm_sub_comm]
    exact normalizedTwoNorm_mul_le_normalizedTwoNorm_mul_norm _ _
  have h2 : normalizedTwoNorm (c * (x * (1 - d))) ≤ ‖x‖ * (‖c‖ * normalizedTwoNorm (d - 1)) := by
    refine (normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm _ _).trans ?_
    rw [mul_left_comm, ← normalizedTwoNorm_sub_comm 1 d]
    exact mul_le_mul_of_nonneg_left (normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm _ _)
      (norm_nonneg c)
  rw [hdecomp, mul_add]
  exact (normalizedTwoNorm_add_le _ _).trans (add_le_add h1 h2)

/-- `‖x - cxc‖₂ ≤ 2‖x‖‖c - 1‖₂` for a contraction `c`; Brown (2006), proof of Lemma 2.7, applies
it to a positive contraction. -/
theorem normalizedTwoNorm_sub_mul_mul_le_of_norm_le_one [DecidableEq n] (x : CStarMatrix n n ℂ)
    {c : CStarMatrix n n ℂ} (hc : ‖c‖ ≤ 1) :
    normalizedTwoNorm (x - c * x * c) ≤ 2 * ‖x‖ * normalizedTwoNorm (c - 1) := by
  refine (normalizedTwoNorm_sub_mul_mul_le x c c).trans ?_
  rw [mul_comm 2, mul_assoc, two_mul]
  gcongr
  exact mul_le_of_le_one_left (normalizedTwoNorm_nonneg _) hc

/-- `k tr_k(x) = Tr(x)`, also for `k = 0`, where both sides vanish. -/
theorem card_mul_normalizedTrace (x : CStarMatrix n n ℂ) :
    (Fintype.card n : ℂ) * normalizedTrace x = (ofMatrix.symm x).trace := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  · rw [normalizedTrace_def, mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

section BlockTensor

variable {m : Type*} [Fintype m]

/-- The normalized trace does not depend on the labelling of the index type. -/
@[simp]
theorem normalizedTrace_reindexₐ (x : CStarMatrix n n ℂ) (e : n ≃ m) :
    normalizedTrace (reindexₐ ℂ ℂ e x) = normalizedTrace x := by
  rw [normalizedTrace_eq_sum, normalizedTrace_eq_sum, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e.symm _ _ fun i ↦ reindexₐ_apply_apply e x i i

/-- The normalized trace is invariant under the inverse of a reindexing. -/
@[simp]
theorem normalizedTrace_reindexₐ_symm (x : CStarMatrix n n ℂ) (e : m ≃ n) :
    normalizedTrace ((reindexₐ ℂ ℂ e).symm x) = normalizedTrace x := by
  rw [← reindexₐ_symm, normalizedTrace_reindexₐ]

open scoped CStarAlgebra in
/-- The normalized trace is invariant under reindexing: its pullback along the reindexing star
isomorphism of an equivalence `n ≃ m` is the normalized trace on `CStarMatrix n n ℂ`. -/
@[simp]
theorem normalizedTraceMap_comp_reindexₐ (e : n ≃ m) :
    (normalizedTraceMap m).comp (.ofClass (reindexₐ ℂ ℂ e)) = normalizedTraceMap n := by
  ext x
  simp

/-- The normalized 2-norm does not depend on the labelling of the index type. -/
@[simp]
theorem normalizedTwoNorm_reindexₐ (x : CStarMatrix n n ℂ) (e : n ≃ m) :
    normalizedTwoNorm (reindexₐ ℂ ℂ e x) = normalizedTwoNorm x := by
  rw [normalizedTwoNorm_def, normalizedTwoNorm_def, ← map_star, ← map_mul,
    normalizedTrace_reindexₐ]

/-- The normalized 2-norm is invariant under the inverse of a reindexing. -/
@[simp]
theorem normalizedTwoNorm_reindexₐ_symm (x : CStarMatrix n n ℂ) (e : m ≃ n) :
    normalizedTwoNorm ((reindexₐ ℂ ℂ e).symm x) = normalizedTwoNorm x := by
  rw [← reindexₐ_symm, normalizedTwoNorm_reindexₐ]

/-- **Block additivity of the normalized trace**, for a block matrix with diagonal blocks
`A ∈ M_k` and `D ∈ M_l`: `tr_{k+l} = (k tr_k(A) + l tr_l(D))/(k + l)`; the off-diagonal blocks do
not contribute. -/
@[simp]
theorem normalizedTrace_ofMatrix_fromBlocks (A : Matrix n n ℂ) (b : Matrix n m ℂ)
    (c : Matrix m n ℂ) (D : Matrix m m ℂ) :
    normalizedTrace (ofMatrix (Matrix.fromBlocks A b c D)) =
      (Fintype.card n * normalizedTrace (ofMatrix A) +
          Fintype.card m * normalizedTrace (ofMatrix D)) /
        (Fintype.card n + Fintype.card m) := by
  rw [card_mul_normalizedTrace, card_mul_normalizedTrace, normalizedTrace_def,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.trace_fromBlocks, Fintype.card_sum, Nat.cast_add, inv_mul_eq_div]

/-- **Block additivity of the normalized trace.** For the block matrix with diagonal blocks
`x ∈ M_k` and `y ∈ M_l`, `tr_{k+l} = (k tr_k(x) + l tr_l(y))/(k + l)`; the off-diagonal blocks do
not contribute. -/
theorem normalizedTrace_fromBlocks (x : CStarMatrix n n ℂ) (b : Matrix n m ℂ) (c : Matrix m n ℂ)
    (y : CStarMatrix m m ℂ) :
    normalizedTrace (ofMatrix (Matrix.fromBlocks (ofMatrix.symm x) b c (ofMatrix.symm y))) =
      (Fintype.card n * normalizedTrace x + Fintype.card m * normalizedTrace y) /
        (Fintype.card n + Fintype.card m) := by
  rw [normalizedTrace_ofMatrix_fromBlocks, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Block additivity of the normalized 2-norm**, for the block-diagonal matrix `A ⊕ D` with
`A ∈ M_k` and `D ∈ M_l`: `‖A ⊕ D‖₂² = (k‖A‖₂² + l‖D‖₂²)/(k + l)`. -/
@[simp]
theorem normalizedTwoNorm_ofMatrix_fromBlocks_sq (A : Matrix n n ℂ) (D : Matrix m m ℂ) :
    normalizedTwoNorm (ofMatrix (Matrix.fromBlocks A 0 0 D)) ^ 2 =
      (Fintype.card n * normalizedTwoNorm (ofMatrix A) ^ 2 +
          Fintype.card m * normalizedTwoNorm (ofMatrix D) ^ 2) /
        (Fintype.card n + Fintype.card m) := by
  have h : star (ofMatrix (Matrix.fromBlocks A 0 0 D)) * ofMatrix (Matrix.fromBlocks A 0 0 D) =
      ofMatrix (Matrix.fromBlocks (ofMatrix.symm (star (ofMatrix A) * ofMatrix A)) 0 0
        (ofMatrix.symm (star (ofMatrix D) * ofMatrix D))) := by
    apply ofMatrix.symm.injective
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  rw [normalizedTwoNorm_sq, h, normalizedTrace_fromBlocks, normalizedTrace_star_mul_self,
    normalizedTrace_star_mul_self]
  norm_cast

/-- **Block additivity of the normalized 2-norm.** For the block-diagonal matrix `x ⊕ y` with
`x ∈ M_k` and `y ∈ M_l`, `‖x ⊕ y‖₂² = (k‖x‖₂² + l‖y‖₂²)/(k + l)`. -/
theorem normalizedTwoNorm_fromBlocks_sq (x : CStarMatrix n n ℂ) (y : CStarMatrix m m ℂ) :
    normalizedTwoNorm (ofMatrix (Matrix.fromBlocks (ofMatrix.symm x) 0 0 (ofMatrix.symm y))) ^ 2 =
      (Fintype.card n * normalizedTwoNorm x ^ 2 + Fintype.card m * normalizedTwoNorm y ^ 2) /
        (Fintype.card n + Fintype.card m) := by
  rw [normalizedTwoNorm_ofMatrix_fromBlocks_sq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Tensor multiplicativity of the normalized trace**, for matrices `A ∈ M_k` and `B ∈ M_l`:
`tr_{kl}(A ⊗ B) = tr_k(A) tr_l(B)`. -/
@[simp]
theorem normalizedTrace_ofMatrix_kronecker (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    normalizedTrace (ofMatrix (A ⊗ₖ B)) =
      normalizedTrace (ofMatrix A) * normalizedTrace (ofMatrix B) := by
  rw [normalizedTrace_def, normalizedTrace_def, normalizedTrace_def, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.trace_kronecker, Fintype.card_prod]
  push_cast
  ring

/-- **Tensor multiplicativity of the normalized trace.** For the Kronecker product of `x ∈ M_k`
and `y ∈ M_l`, `tr_{kl}(x ⊗ y) = tr_k(x) tr_l(y)`. -/
theorem normalizedTrace_kronecker (x : CStarMatrix n n ℂ) (y : CStarMatrix m m ℂ) :
    normalizedTrace (ofMatrix (ofMatrix.symm x ⊗ₖ ofMatrix.symm y)) =
      normalizedTrace x * normalizedTrace y := by
  rw [normalizedTrace_ofMatrix_kronecker, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Tensor multiplicativity of the normalized 2-norm**, for matrices `A ∈ M_k` and `B ∈ M_l`:
`‖A ⊗ B‖₂ = ‖A‖₂‖B‖₂`. -/
@[simp]
theorem normalizedTwoNorm_ofMatrix_kronecker (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    normalizedTwoNorm (ofMatrix (A ⊗ₖ B)) =
      normalizedTwoNorm (ofMatrix A) * normalizedTwoNorm (ofMatrix B) := by
  have h : star (ofMatrix (A ⊗ₖ B)) * ofMatrix (A ⊗ₖ B) =
      ofMatrix (ofMatrix.symm (star (ofMatrix A) * ofMatrix A) ⊗ₖ
        ofMatrix.symm (star (ofMatrix B) * ofMatrix B)) := by
    apply ofMatrix.symm.injective
    simp [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
  rw [← sq_eq_sq₀ (normalizedTwoNorm_nonneg _)
    (mul_nonneg (normalizedTwoNorm_nonneg _) (normalizedTwoNorm_nonneg _)), mul_pow,
    normalizedTwoNorm_sq, h, normalizedTrace_kronecker, normalizedTrace_star_mul_self,
    normalizedTrace_star_mul_self]
  norm_cast

/-- **Tensor multiplicativity of the normalized 2-norm.** For the Kronecker product of `x ∈ M_k`
and `y ∈ M_l`, `‖x ⊗ y‖₂ = ‖x‖₂‖y‖₂`. -/
theorem normalizedTwoNorm_kronecker (x : CStarMatrix n n ℂ) (y : CStarMatrix m m ℂ) :
    normalizedTwoNorm (ofMatrix (ofMatrix.symm x ⊗ₖ ofMatrix.symm y)) =
      normalizedTwoNorm x * normalizedTwoNorm y := by
  rw [normalizedTwoNorm_ofMatrix_kronecker, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end BlockTensor

end CStarMatrix
