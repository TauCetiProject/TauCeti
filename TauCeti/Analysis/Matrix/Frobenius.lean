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
* `Matrix.frobenius_norm_sq_eq_sum_normSq` — the squared complex Frobenius norm is the sum of
  the squared norms of the entries.
* `Matrix.frobenius_norm_sq_conj_unitary` — unitary conjugation preserves the squared norm.
* `Matrix.abs_apply_le_sqrt_trace_mul_transpose` — each entry of a real matrix is bounded in
  absolute value by the square root of the trace of its Gram matrix `L * Lᵀ`.
-/

public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace Matrix

variable {𝕜 E m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

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

/-- The squared Frobenius norm of a complex matrix is the sum of its entrywise squared norms. -/
theorem frobenius_norm_sq_eq_sum_normSq (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [Real.rpow_two, Complex.normSq_eq_norm_sq]

/-- Unitary conjugation preserves the squared Frobenius norm. -/
theorem frobenius_norm_sq_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U A : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ‖Uᴴ * A * U‖ ^ 2 = ‖A‖ ^ 2 := by
  have hright : U * Uᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using (mem_unitaryGroup_iff.mp hU)
  have hnorm (B : Matrix ι ι ℂ) : ((‖B‖ ^ 2 : ℝ) : ℂ) = (Bᴴ * B).trace := by
    rw [← frobenius_inner_eq_trace_conjTranspose_mul, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [hnorm, hnorm]
  have hmul : (Uᴴ * A * U)ᴴ * (Uᴴ * A * U) = Uᴴ * (Aᴴ * A) * U := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ, hright, one_mul]
  rw [hmul, trace_mul_cycle, hright, one_mul]

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
