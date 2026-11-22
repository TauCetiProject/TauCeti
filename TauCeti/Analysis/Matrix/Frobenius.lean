/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Frobenius inner product on matrices

Mathlib's `Matrix.frobeniusSeminormedAddCommGroup` equips `Matrix m n E` with the Frobenius norm
while keeping the topology and uniformity definitionally equal to the product ones. When `E` is an
inner product space over `𝕜`, this file adds the compatible inner product
`⟪A, B⟫_𝕜 = ∑ i, ∑ j, ⟪A i j, B i j⟫_𝕜`; for `E = 𝕜` it is the trace pairing `(Aᴴ * B).trace`.

Like the Frobenius norm itself, the inner product is not a global instance, because there are
several natural norms on matrices. It is registered as a scoped instance in the existing
`Matrix.Norms.Frobenius` namespace, so `open scoped Matrix.Norms.Frobenius` activates the norm
and the inner product together.

## Main declarations

* `Matrix.re_trace_mul_conjTranspose_self` — the real trace of `X * Xᴴ` is the sum of the
  squared entry norms.
* `Matrix.frobeniusInnerProductSpace` — the Frobenius inner product, compatible with
  `Matrix.frobeniusSeminormedAddCommGroup`.
* `Matrix.frobenius_inner_def` — the inner product is the sum of the entrywise inner products.
* `Matrix.frobenius_inner_smul_left` — the inner product is conjugate-linear in its first argument
  for the entrywise scalar action on matrices.
* `Matrix.frobenius_inner_eq_sum_conj_mul`, `Matrix.frobenius_real_inner_eq_sum_mul` — over `𝕜`
  itself, the inner product is `∑ i, ∑ j, conj (A i j) * B i j`, and over `ℝ` it is
  `∑ i, ∑ j, A i j * B i j`.
* `Matrix.frobenius_inner_eq_trace_conjTranspose_mul` — over `𝕜` itself, the inner product is
  `(Aᴴ * B).trace`.
* `Matrix.frobenius_real_inner_eq_re_trace_conjTranspose_mul` — the real inner product is
  `Re tr(Aᴴ * B)`.
* `Matrix.UnitaryGroup.frobenius_inner_mul_left` and
  `Matrix.UnitaryGroup.frobenius_inner_mul_right` — left and right unitary multiplication preserve
  the Frobenius inner product on rectangular matrices. In particular, unitary conjugation
  preserves the scalar and real inner products (`Matrix.UnitaryGroup.frobenius_inner_conj` and
  `Matrix.UnitaryGroup.frobenius_real_inner_conj`).
* `Matrix.frobenius_inner_lie_left` — the adjoint of commutation by `X` is commutation by `Xᴴ`.

* `Matrix.frobenius_norm_sq_eq_sum_normSq` — the squared complex Frobenius norm is the sum of
  the squared norms of the entries.
* `Matrix.frobenius_norm_sq_conj_unitary` — unitary conjugation preserves the squared norm.
* `Matrix.abs_apply_le_sqrt_trace_mul_transpose` — each entry of a real matrix is bounded in
  absolute value by the square root of the trace of its Gram matrix `L * Lᵀ`.

## The skew-Hermitian trace metric

The real Frobenius inner product restricts to `-Re tr(XY)` on skew-Hermitian matrices, with
quadratic form the squared Frobenius norm. Unitary conjugation preserves the metric, including
for disconnected unitary subgroups; commutation by a skew-Hermitian matrix is skew-adjoint.
The trace-metric convention follows Oh–Tataru, *The hyperbolic Yang–Mills equation for connections
in an arbitrary topological class*, Comm. Math. Phys. 365 (2019), §6.1.
-/

public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace Matrix

variable {𝕜 E m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The real part of the trace of `X * Xᴴ` is the sum of the squared entry norms. -/
theorem re_trace_mul_conjTranspose_self (X : Matrix m n 𝕜) :
    RCLike.re (Matrix.trace (X * X.conjTranspose)) = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, RCLike.mul_conj]

section Def

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Frobenius inner product `⟪A, B⟫_𝕜 = ∑ i, ∑ j, ⟪A i j, B i j⟫_𝕜` on matrices with entries
in an inner product space, compatible with the Frobenius norm of
`Matrix.frobeniusSeminormedAddCommGroup`. Not declared as a global instance because there are
several natural choices of norm on matrices; it is available through
`open scoped Matrix.Norms.Frobenius`. -/
@[instance_reducible]
def frobeniusInnerProductSpace :
    letI : SeminormedAddCommGroup (Matrix m n E) := frobeniusSeminormedAddCommGroup
    InnerProductSpace 𝕜 (Matrix m n E) :=
  letI : SeminormedAddCommGroup (Matrix m n E) := frobeniusSeminormedAddCommGroup
  { __ := (frobeniusNormedSpace : NormedSpace 𝕜 (Matrix m n E))
    inner A B := ∑ i, ∑ j, ⟪A i j, B i j⟫_𝕜
    norm_sq_eq_re_inner A := by
      rw [frobenius_norm_def, ← Real.rpow_natCast,
        ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)]
      simp [map_sum]
    conj_inner_symm A B := by simp
    add_left A B C := by simp [inner_add_left, Finset.sum_add_distrib]
    smul_left A B r := by simp [inner_smul_left, Finset.mul_sum] }

namespace Norms.Frobenius

attribute [scoped instance] Matrix.frobeniusInnerProductSpace

end Norms.Frobenius

open scoped Matrix.Norms.Frobenius

/-- The Frobenius inner product is the sum of the entrywise inner products. -/
@[simp]
theorem frobenius_inner_def (A B : Matrix m n E) :
    ⟪A, B⟫_𝕜 = ∑ i, ∑ j, ⟪A i j, B i j⟫_𝕜 :=
  (rfl)

/-- The Frobenius inner product is conjugate-linear in its first argument for the entrywise scalar
action on matrices. -/
theorem frobenius_inner_smul_left (r : 𝕜) (A B : Matrix m n E) :
    ⟪r • A, B⟫_𝕜 = conj r * ⟪A, B⟫_𝕜 := by
  simp [inner_smul_left, Finset.mul_sum]

end Def

open scoped Matrix Matrix.Norms.Frobenius

/-- The Frobenius inner product of matrices over `𝕜` is `∑ i, ∑ j, conj (A i j) * B i j`. -/
theorem frobenius_inner_eq_sum_conj_mul (A B : Matrix m n 𝕜) :
    ⟪A, B⟫_𝕜 = ∑ i, ∑ j, conj (A i j) * B i j := by
  simp only [frobenius_inner_def, RCLike.inner_apply']

/-- The Frobenius inner product of real matrices is `∑ i, ∑ j, A i j * B i j`. -/
theorem frobenius_real_inner_eq_sum_mul (A B : Matrix m n ℝ) :
    ⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j := by
  simp only [frobenius_inner_eq_sum_conj_mul, conj_trivial]

/-- The Frobenius inner product of matrices over `𝕜` is the trace of `Aᴴ * B`. -/
theorem frobenius_inner_eq_trace_conjTranspose_mul (A B : Matrix m n 𝕜) :
    ⟪A, B⟫_𝕜 = (Aᴴ * B).trace := by
  simp only [frobenius_inner_eq_sum_conj_mul, trace, diag_apply, Matrix.mul_apply,
    conjTranspose_apply,
    RCLike.star_def]
  exact Finset.sum_comm

/-- The real Frobenius inner product is the real part of the scalar Frobenius inner product. -/
theorem frobenius_real_inner_eq_re_inner (X Y : Matrix m n 𝕜) :
    ⟪X, Y⟫_ℝ = RCLike.re ⟪X, Y⟫_𝕜 := by
  simp only [frobenius_inner_def, real_inner_eq_re_inner 𝕜, map_sum]

/-- The real Frobenius inner product is the real part of the trace pairing. -/
theorem frobenius_real_inner_eq_re_trace_conjTranspose_mul (X Y : Matrix m n 𝕜) :
    ⟪X, Y⟫_ℝ = RCLike.re (Xᴴ * Y).trace := by
  rw [frobenius_real_inner_eq_re_inner, frobenius_inner_eq_trace_conjTranspose_mul]

/-- Left multiplication by a unitary matrix preserves the Frobenius inner product. -/
theorem UnitaryGroup.frobenius_inner_mul_left [DecidableEq m]
    (U : Matrix.unitaryGroup m 𝕜) (X Y : Matrix m n 𝕜) :
    ⟪(U : Matrix m m 𝕜) * X, (U : Matrix m m 𝕜) * Y⟫_𝕜 = ⟪X, Y⟫_𝕜 := by
  have hU : (U : Matrix m m 𝕜)ᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using UnitaryGroup.star_mul_self U
  simp only [frobenius_inner_eq_trace_conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Matrix m m 𝕜)ᴴ (U : Matrix m m 𝕜), hU, Matrix.one_mul]

/-- Right multiplication by a unitary matrix preserves the Frobenius inner product. -/
theorem UnitaryGroup.frobenius_inner_mul_right [DecidableEq n]
    (U : Matrix.unitaryGroup n 𝕜) (X Y : Matrix m n 𝕜) :
    ⟪X * (U : Matrix n n 𝕜), Y * (U : Matrix n n 𝕜)⟫_𝕜 = ⟪X, Y⟫_𝕜 := by
  have hU : (U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp U.property
  simp only [frobenius_inner_eq_trace_conjTranspose_mul, conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, ← Matrix.mul_assoc, trace_mul_cycle, hU, one_mul]

/-- Unitary conjugation preserves the Frobenius inner product. -/
@[simp↓]
theorem UnitaryGroup.frobenius_inner_conj [DecidableEq n]
    (U : Matrix.unitaryGroup n 𝕜) (X Y : Matrix n n 𝕜) :
    ⟪(U : Matrix n n 𝕜) * X * (U : Matrix n n 𝕜)ᴴ,
      (U : Matrix n n 𝕜) * Y * (U : Matrix n n 𝕜)ᴴ⟫_𝕜 = ⟪X, Y⟫_𝕜 := by
  simpa only [UnitaryGroup.inv_val, star_eq_conjTranspose, UnitaryGroup.frobenius_inner_mul_left]
    using UnitaryGroup.frobenius_inner_mul_right U⁻¹
      ((U : Matrix n n 𝕜) * X) ((U : Matrix n n 𝕜) * Y)

/-- Unitary conjugation preserves the real Frobenius inner product. -/
@[simp↓]
theorem UnitaryGroup.frobenius_real_inner_conj [DecidableEq n]
    (U : Matrix.unitaryGroup n 𝕜) (X Y : Matrix n n 𝕜) :
    ⟪(U : Matrix n n 𝕜) * X * (U : Matrix n n 𝕜)ᴴ,
      (U : Matrix n n 𝕜) * Y * (U : Matrix n n 𝕜)ᴴ⟫_ℝ = ⟪X, Y⟫_ℝ := by
  simp only [frobenius_real_inner_eq_re_inner (𝕜 := 𝕜), UnitaryGroup.frobenius_inner_conj]

/-- The Frobenius inner product with a skew-Hermitian first argument is `-tr(XY)`. -/
theorem frobenius_inner_eq_neg_trace_mul_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y : Matrix n n 𝕜) : ⟪X, Y⟫_𝕜 = -(X * Y).trace := by
  rw [frobenius_inner_eq_trace_conjTranspose_mul, hX, neg_mul, trace_neg]

/-- The real Frobenius inner product with a skew-Hermitian first argument is `-Re tr(XY)`. -/
theorem frobenius_real_inner_eq_neg_re_trace_mul_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y : Matrix n n 𝕜) : ⟪X, Y⟫_ℝ = -RCLike.re (X * Y).trace := by
  rw [frobenius_real_inner_eq_re_inner,
    frobenius_inner_eq_neg_trace_mul_of_conjTranspose_eq_neg hX, map_neg]

/-- For a skew-Hermitian matrix `X`, `-tr(X²)` is its squared Frobenius norm in `𝕜`. -/
theorem neg_trace_mul_self_eq_frobenius_norm_sq_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) : -(X * X).trace = (‖X‖ : 𝕜) ^ 2 := by
  rw [← frobenius_inner_eq_neg_trace_mul_of_conjTranspose_eq_neg hX, inner_self_eq_norm_sq_to_K]

/-- On skew-Hermitian matrices the trace metric has the squared Frobenius norm as its quadratic
form, hence is positive definite. -/
theorem neg_re_trace_mul_self_eq_frobenius_norm_sq_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) : -RCLike.re (X * X).trace = ‖X‖ ^ 2 := by
  rw [← map_neg, neg_trace_mul_self_eq_frobenius_norm_sq_of_conjTranspose_eq_neg hX,
    RCLike.re_ofReal_pow]

/-- Commutation by `Xᴴ` is adjoint to commutation by `X` for the Frobenius inner product. -/
theorem frobenius_inner_lie_left (X Y Z : Matrix n n 𝕜) :
    ⟪⁅X, Y⁆, Z⟫_𝕜 = ⟪Y, ⁅Xᴴ, Z⁆⟫_𝕜 := by
  simp only [Ring.lie_def, frobenius_inner_eq_trace_conjTranspose_mul,
    conjTranspose_sub, conjTranspose_mul, sub_mul, mul_sub, trace_sub, Matrix.mul_assoc]
  rw [← trace_mul_cycle' Yᴴ Z Xᴴ]

/-- Commutation by a skew-Hermitian matrix is skew-adjoint for the Frobenius inner product. -/
theorem frobenius_inner_lie_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y Z : Matrix n n 𝕜) : ⟪⁅X, Y⁆, Z⟫_𝕜 = -⟪Y, ⁅X, Z⁆⟫_𝕜 := by
  rw [frobenius_inner_lie_left, hX, ← inner_neg_right]
  congr 1
  simp only [Ring.lie_def, neg_mul, mul_neg, neg_sub_neg, neg_sub]

/-- Commutation by a skew-Hermitian matrix is skew-adjoint for the real Frobenius inner
product. -/
theorem frobenius_real_inner_lie_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y Z : Matrix n n 𝕜) : ⟪⁅X, Y⁆, Z⟫_ℝ = -⟪Y, ⁅X, Z⁆⟫_ℝ := by
  simp only [frobenius_real_inner_eq_re_inner (𝕜 := 𝕜),
    frobenius_inner_lie_of_conjTranspose_eq_neg hX, map_neg]

/-- The squared Frobenius norm of a complex matrix is the sum of its entrywise squared norms. -/
theorem frobenius_norm_sq_eq_sum_normSq (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [Real.rpow_two, Complex.normSq_eq_norm_sq]

/-- Unitary conjugation preserves the squared Frobenius norm. -/
theorem frobenius_norm_sq_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U A : Matrix ι ι 𝕜) (hU : U ∈ Matrix.unitaryGroup ι 𝕜) :
    ‖Uᴴ * A * U‖ ^ 2 = ‖A‖ ^ 2 := by
  simpa only [UnitaryGroup.inv_val, Subtype.coe_mk, star_eq_conjTranspose,
    conjTranspose_conjTranspose, real_inner_self_eq_norm_sq] using
    UnitaryGroup.frobenius_real_inner_conj (⟨U, hU⟩ : Matrix.unitaryGroup ι 𝕜)⁻¹ A A

open scoped Matrix.Norms.Frobenius in
/-- Each entry of a real matrix is bounded in absolute value by the square root of the trace of
its Gram matrix `L * Lᵀ`. -/
theorem abs_apply_le_sqrt_trace_mul_transpose (L : Matrix m n ℝ) (i : m) (j : n) :
    |L i j| ≤ √(L * Lᵀ).trace := by
  rw [← Real.norm_eq_abs]
  refine (norm_apply_le_frobenius_norm L i j).trans (le_of_eq ?_)
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp [trace, Matrix.mul_apply, sq]

end Matrix
