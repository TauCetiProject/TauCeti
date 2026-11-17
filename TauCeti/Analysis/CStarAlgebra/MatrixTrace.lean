/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.Matrix.Frobenius
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.MatrixOrder

/-!
# The normalized trace and 2-norm on matrix algebras

On the matrix C⋆-algebra `M_k = CStarMatrix (Fin k) (Fin k) ℂ`, with its operator norm, this file
defines the normalized trace `tr_k(x) = k⁻¹ Tr(x)` and the normalized 2-norm
`‖x‖₂ = tr_k(x⋆x)^{1/2}`, and proves the comparison inequalities between `‖·‖₂` and the operator
norm `‖·‖` that are used to measure multiplicativity defects of completely positive maps into
matrix algebras.

The 2-norm is `k^{-1/2}` times the Frobenius norm, and `tr_k(x⋆y) = k⁻¹⟪x, y⟫_F` for the complex
Frobenius inner product `Matrix.frobeniusInnerProductSpace`, so the norm axioms and the
Cauchy–Schwarz inequality come from that inner product space. The comparisons with the operator
norm come from the C⋆-order: `x⋆x ≤ ‖x‖²` and the trace is monotone.

## Main declarations

* `TauCeti.Mat k`: the matrix C⋆-algebra `CStarMatrix (Fin k) (Fin k) ℂ`.
* `TauCeti.matrixTrace`: the normalized trace `tr_k`, with `tr_k(1) = 1` for `k ≠ 0`,
  `tr_k(xy) = tr_k(yx)` and monotonicity for the C⋆-order.
* `TauCeti.matrixTwoNorm`: the normalized 2-norm `‖x‖₂`.
* `TauCeti.matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm`: `‖x‖₂ = k^{-1/2}‖x‖_F`.
* `TauCeti.matrixTwoNormAddGroupNorm`: `‖·‖₂` is a norm.
* `TauCeti.norm_matrixTrace_star_mul_le`: Cauchy–Schwarz `|tr_k(x⋆y)| ≤ ‖x‖₂‖y‖₂`, and
  `TauCeti.norm_matrixTrace_le_matrixTwoNorm`: `|tr_k(x)| ≤ ‖x‖₂`.
* `TauCeti.matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm`,
  `TauCeti.matrixTwoNorm_mul_le_matrixTwoNorm_mul_norm`, `TauCeti.matrixTwoNorm_le_norm`,
  `TauCeti.matrixTwoNorm_star`: `‖xy‖₂ ≤ ‖x‖‖y‖₂`, `‖xy‖₂ ≤ ‖x‖₂‖y‖`, `‖x‖₂ ≤ ‖x‖` and
  `‖x⋆‖₂ = ‖x‖₂`.
* `TauCeti.matrixTwoNorm_sub_mul_mul_le`: `‖x - cxc‖₂ ≤ 2‖x‖‖c - 1‖₂` for a contraction `c`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), Chapter 2 and Lemma 2.7.
-/

public section

noncomputable section

open CStarMatrix Matrix
open scoped ComplexOrder InnerProductSpace Matrix.Norms.Frobenius

namespace TauCeti

/-- The full matrix algebra `M_k = CStarMatrix (Fin k) (Fin k) ℂ`, with its operator norm. -/
abbrev Mat (k : ℕ) : Type := CStarMatrix (Fin k) (Fin k) ℂ

variable {k : ℕ}

/-- The normalized trace `tr_k(x) = k⁻¹ Σᵢ xᵢᵢ` on `M_k`, the unique tracial state of `M_k` for
`k ≥ 1`; `tr_0 = 0`. In `M_2`, `tr_2(1) = 1` and `tr_2(e₁₁) = 1/2`. -/
def matrixTrace (x : Mat k) : ℂ :=
  (k : ℂ)⁻¹ * (ofMatrix.symm x).trace

/-- Unfolding lemma for `matrixTrace`. -/
theorem matrixTrace_def (x : Mat k) : matrixTrace x = (k : ℂ)⁻¹ * (ofMatrix.symm x).trace :=
  (rfl)

/-- The normalized trace is the averaged sum of the diagonal entries. -/
theorem matrixTrace_eq_sum (x : Mat k) : matrixTrace x = (k : ℂ)⁻¹ * ∑ i, x i i :=
  (rfl)

/-- The normalized trace of `0` is `0`. -/
@[simp]
theorem matrixTrace_zero : matrixTrace (0 : Mat k) = 0 := by
  rw [matrixTrace_def, show ofMatrix.symm (0 : Mat k) = 0 from rfl, trace_zero, mul_zero]

/-- The normalized trace is additive. -/
theorem matrixTrace_add (x y : Mat k) : matrixTrace (x + y) = matrixTrace x + matrixTrace y := by
  rw [matrixTrace_def, matrixTrace_def, matrixTrace_def, ← mul_add, ← trace_add]
  rfl

/-- The normalized trace commutes with subtraction. -/
theorem matrixTrace_sub (x y : Mat k) : matrixTrace (x - y) = matrixTrace x - matrixTrace y := by
  rw [matrixTrace_def, matrixTrace_def, matrixTrace_def, ← mul_sub, ← trace_sub]
  rfl

/-- The normalized trace is complex-linear. -/
theorem matrixTrace_smul (c : ℂ) (x : Mat k) : matrixTrace (c • x) = c * matrixTrace x := by
  simp only [matrixTrace_def]
  rw [mul_left_comm]
  exact congrArg _ (Matrix.trace_smul c (ofMatrix.symm x))

/-- The normalized trace of the identity of `M_k` is `1` for `k ≠ 0`. -/
@[simp]
theorem matrixTrace_one [NeZero k] : matrixTrace (1 : Mat k) = 1 := by
  have : (ofMatrix.symm (1 : Mat k)) = 1 := rfl
  rw [matrixTrace_def, this, Matrix.trace_one, Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne k))

/-- The normalized trace is tracial. -/
theorem matrixTrace_mul_comm (x y : Mat k) : matrixTrace (x * y) = matrixTrace (y * x) := by
  rw [matrixTrace_def, matrixTrace_def, ofMatrix_symm_mul, ofMatrix_symm_mul,
    Matrix.trace_mul_comm]

/-- The normalized trace of the adjoint is the conjugate of the normalized trace. -/
theorem matrixTrace_star (x : Mat k) : matrixTrace (star x) = star (matrixTrace x) := by
  simp [matrixTrace_def, Matrix.trace_conjTranspose]

/-- The normalized trace is invariant under unitary conjugation. -/
theorem matrixTrace_unitary_conj {u : Mat k} (hu : u ∈ unitary (Mat k)) (x : Mat k) :
    matrixTrace (u * x * star u) = matrixTrace x := by
  rw [matrixTrace_mul_comm, ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]

/-- The normalized trace of a positive matrix is nonnegative. -/
theorem matrixTrace_nonneg {x : Mat k} (hx : 0 ≤ x) : 0 ≤ matrixTrace x := by
  rw [matrixTrace_def]
  exact mul_nonneg (by simp) (nonneg_iff_posSemidef.mp hx).trace_nonneg

/-- The normalized trace is monotone for the C⋆-order of `M_k`. -/
theorem matrixTrace_mono {x y : Mat k} (h : x ≤ y) : matrixTrace x ≤ matrixTrace y := by
  have := matrixTrace_nonneg (sub_nonneg.mpr h)
  rwa [matrixTrace_sub, sub_nonneg] at this

/-- `tr_k(x⋆y) = k⁻¹⟪x, y⟫_F` for the complex Frobenius inner product. -/
theorem matrixTrace_star_mul (x y : Mat k) :
    matrixTrace (star x * y) = (k : ℂ)⁻¹ * ⟪ofMatrix.symm x, ofMatrix.symm y⟫_ℂ := by
  rw [matrixTrace_def, frobenius_inner_eq_trace_conjTranspose_mul, ofMatrix_symm_mul,
    ofMatrix_symm_star]

/-- The normalized 2-norm `‖x‖₂ = tr_k(x⋆x)^{1/2}` on `M_k`, `k^{-1/2}` times the Frobenius norm.
In `M_2`, `‖e₁₁‖₂ = 2^{-1/2}`. -/
def matrixTwoNorm (x : Mat k) : ℝ :=
  Real.sqrt (matrixTrace (star x * x)).re

/-- Unfolding lemma for `matrixTwoNorm`. -/
theorem matrixTwoNorm_def (x : Mat k) :
    matrixTwoNorm x = Real.sqrt (matrixTrace (star x * x)).re :=
  (rfl)

/-- The normalized 2-norm is `k^{-1/2}` times the Frobenius norm. -/
theorem matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm (x : Mat k) :
    matrixTwoNorm x = (Real.sqrt k)⁻¹ * ‖ofMatrix.symm x‖ := by
  have h : (matrixTrace (star x * x)).re = (k : ℝ)⁻¹ * ‖ofMatrix.symm x‖ ^ 2 := by
    rw [matrixTrace_star_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [matrixTwoNorm_def, h, Real.sqrt_mul (by positivity), Real.sqrt_inv,
    Real.sqrt_sq (norm_nonneg _)]

/-- The normalized 2-norm is nonnegative. -/
theorem matrixTwoNorm_nonneg (x : Mat k) : 0 ≤ matrixTwoNorm x :=
  Real.sqrt_nonneg _

/-- `tr_k(x⋆x) = ‖x‖₂²`. -/
theorem matrixTrace_star_mul_self (x : Mat k) :
    matrixTrace (star x * x) = ((matrixTwoNorm x ^ 2 : ℝ) : ℂ) := by
  rw [matrixTrace_star_mul, inner_self_eq_norm_sq_to_K,
    matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg k)]
  push_cast
  rfl

/-- `‖x‖₂² = Re tr_k(x⋆x)`. -/
theorem matrixTwoNorm_sq (x : Mat k) : matrixTwoNorm x ^ 2 = (matrixTrace (star x * x)).re := by
  rw [matrixTrace_star_mul_self, Complex.ofReal_re]

/-- `‖0‖₂ = 0`. -/
@[simp]
theorem matrixTwoNorm_zero : matrixTwoNorm (0 : Mat k) = 0 := by
  simp [matrixTwoNorm_def]

/-- The normalized 2-norm is definite. -/
theorem matrixTwoNorm_eq_zero_iff {x : Mat k} : matrixTwoNorm x = 0 ↔ x = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact iff_of_true (by simp [matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm])
      (CStarMatrix.ext fun i _ ↦ i.elim0)
  · have : (Real.sqrt k)⁻¹ ≠ 0 := by positivity
    rw [matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_eq_zero, or_iff_right this, norm_eq_zero]
    exact ofMatrix.symm.injective.eq_iff' rfl

/-- The triangle inequality for the normalized 2-norm. -/
theorem matrixTwoNorm_add_le (x y : Mat k) :
    matrixTwoNorm (x + y) ≤ matrixTwoNorm x + matrixTwoNorm y := by
  simp only [matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- The normalized 2-norm is absolutely homogeneous. -/
theorem matrixTwoNorm_smul (c : ℂ) (x : Mat k) : matrixTwoNorm (c • x) = ‖c‖ * matrixTwoNorm x := by
  simp only [matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm, mul_left_comm ‖c‖]
  exact congrArg _ (norm_smul c (ofMatrix.symm x))

/-- `‖-x‖₂ = ‖x‖₂`. -/
@[simp]
theorem matrixTwoNorm_neg (x : Mat k) : matrixTwoNorm (-x) = matrixTwoNorm x := by
  simpa using matrixTwoNorm_smul (-1) x

/-- `‖x - y‖₂ = ‖y - x‖₂`. -/
theorem matrixTwoNorm_sub_comm (x y : Mat k) : matrixTwoNorm (x - y) = matrixTwoNorm (y - x) := by
  rw [← neg_sub, matrixTwoNorm_neg]

/-- The normalized 2-norm as an additive group norm on `M_k`. It is not registered as an instance,
since `M_k` carries its operator norm. -/
def matrixTwoNormAddGroupNorm (k : ℕ) : AddGroupNorm (Mat k) where
  toFun := matrixTwoNorm
  map_zero' := matrixTwoNorm_zero
  add_le' := matrixTwoNorm_add_le
  neg' := matrixTwoNorm_neg
  eq_zero_of_map_eq_zero' _ := matrixTwoNorm_eq_zero_iff.mp

/-- `matrixTwoNormAddGroupNorm k` evaluates to the normalized 2-norm. -/
@[simp]
theorem matrixTwoNormAddGroupNorm_apply (x : Mat k) :
    matrixTwoNormAddGroupNorm k x = matrixTwoNorm x :=
  (rfl)

/-- The Cauchy–Schwarz inequality `|tr_k(x⋆y)| ≤ ‖x‖₂‖y‖₂`. -/
theorem norm_matrixTrace_star_mul_le (x y : Mat k) :
    ‖matrixTrace (star x * y)‖ ≤ matrixTwoNorm x * matrixTwoNorm y := by
  rw [matrixTrace_star_mul, norm_mul, norm_inv, Complex.norm_natCast,
    matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm, matrixTwoNorm_eq_inv_sqrt_mul_frobenius_norm,
    mul_mul_mul_comm, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg k)]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)

/-- `‖1‖₂ = 1` in `M_k` for `k ≠ 0`. -/
@[simp]
theorem matrixTwoNorm_one [NeZero k] : matrixTwoNorm (1 : Mat k) = 1 := by
  rw [matrixTwoNorm_def, star_one, one_mul, matrixTrace_one, Complex.one_re, Real.sqrt_one]

/-- `‖1‖₂ ≤ 1` in every `M_k`, with equality unless `k = 0`. -/
theorem matrixTwoNorm_one_le : matrixTwoNorm (1 : Mat k) ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [show (1 : Mat 0) = 0 from CStarMatrix.ext fun i _ ↦ i.elim0]
  · have : NeZero k := ⟨hk⟩
    simp

/-- `|tr_k(x)| ≤ ‖x‖₂`, Cauchy–Schwarz against the identity. -/
theorem norm_matrixTrace_le_matrixTwoNorm (x : Mat k) : ‖matrixTrace x‖ ≤ matrixTwoNorm x := by
  simpa using (norm_matrixTrace_star_mul_le 1 x).trans
    (mul_le_of_le_one_left (matrixTwoNorm_nonneg x) matrixTwoNorm_one_le)

/-- The normalized 2-norm is invariant under the adjoint. -/
@[simp]
theorem matrixTwoNorm_star (x : Mat k) : matrixTwoNorm (star x) = matrixTwoNorm x := by
  rw [matrixTwoNorm_def, matrixTwoNorm_def, star_star, matrixTrace_mul_comm]

/-- `‖xy‖₂ ≤ ‖x‖‖y‖₂`. -/
theorem matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm (x y : Mat k) :
    matrixTwoNorm (x * y) ≤ ‖x‖ * matrixTwoNorm y := by
  have hx : star x * x ≤ ((‖x‖ ^ 2 : ℝ) : ℂ) • (1 : Mat k) := by
    convert CStarAlgebra.star_mul_le_algebraMap_norm_sq x using 1
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have h : star (x * y) * (x * y) ≤ ((‖x‖ ^ 2 : ℝ) : ℂ) • (star y * y) :=
    calc star (x * y) * (x * y) = star y * (star x * x) * y := by simp only [star_mul, mul_assoc]
      _ ≤ star y * (((‖x‖ ^ 2 : ℝ) : ℂ) • 1) * y := star_left_conjugate_le_conjugate hx y
      _ = _ := by rw [mul_smul_comm, mul_one, smul_mul_assoc]
  have h2 := Complex.re_le_re (matrixTrace_mono h)
  rw [matrixTrace_smul, matrixTrace_star_mul_self, matrixTrace_star_mul_self,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re, ← mul_pow] at h2
  exact pow_le_pow_iff_left₀ (matrixTwoNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (matrixTwoNorm_nonneg _)) two_ne_zero |>.mp h2

/-- `‖xy‖₂ ≤ ‖x‖₂‖y‖`. -/
theorem matrixTwoNorm_mul_le_matrixTwoNorm_mul_norm (x y : Mat k) :
    matrixTwoNorm (x * y) ≤ matrixTwoNorm x * ‖y‖ := by
  rw [← matrixTwoNorm_star, star_mul, mul_comm, ← norm_star y, ← matrixTwoNorm_star x]
  exact matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm _ _

/-- `‖x‖₂ ≤ ‖x‖`. -/
theorem matrixTwoNorm_le_norm (x : Mat k) : matrixTwoNorm x ≤ ‖x‖ := by
  simpa using (matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm x 1).trans
    (mul_le_of_le_one_right (norm_nonneg x) matrixTwoNorm_one_le)

/-- The normalized 2-norm is invariant under unitary conjugation. -/
theorem matrixTwoNorm_unitary_conj {u : Mat k} (hu : u ∈ unitary (Mat k)) (x : Mat k) :
    matrixTwoNorm (u * x * star u) = matrixTwoNorm x := by
  have : star (u * x * star u) * (u * x * star u) = u * (star x * x) * star u := by
    simp only [star_mul, star_star, mul_assoc, Unitary.star_mul_self_of_mem hu,
      ← mul_assoc (star u) u, one_mul]
  rw [matrixTwoNorm_def, matrixTwoNorm_def, this, matrixTrace_unitary_conj hu]

/-- `‖x - cxc‖₂ ≤ 2‖x‖‖c - 1‖₂` for a contraction `c` (brown2006, Lemma 2.7, stated there for
positive contractions). -/
theorem matrixTwoNorm_sub_mul_mul_le (x : Mat k) {c : Mat k} (hc : ‖c‖ ≤ 1) :
    matrixTwoNorm (x - c * x * c) ≤ 2 * ‖x‖ * matrixTwoNorm (c - 1) := by
  have hdecomp : x - c * x * c = (1 - c) * x + c * (x * (1 - c)) := by noncomm_ring
  have h1 : matrixTwoNorm ((1 - c) * x) ≤ ‖x‖ * matrixTwoNorm (c - 1) := by
    rw [mul_comm, matrixTwoNorm_sub_comm]
    exact matrixTwoNorm_mul_le_matrixTwoNorm_mul_norm _ _
  have h2 : matrixTwoNorm (c * (x * (1 - c))) ≤ ‖x‖ * matrixTwoNorm (c - 1) := by
    refine (matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm _ _).trans ?_
    refine (mul_le_of_le_one_left (matrixTwoNorm_nonneg _) hc).trans ?_
    rw [← matrixTwoNorm_sub_comm 1 c]
    exact matrixTwoNorm_mul_le_norm_mul_matrixTwoNorm _ _
  rw [hdecomp, two_mul, add_mul]
  exact (matrixTwoNorm_add_le _ _).trans (add_le_add h1 h2)

end TauCeti
