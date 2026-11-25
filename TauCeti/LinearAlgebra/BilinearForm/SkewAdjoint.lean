/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Traces of endomorphisms times their adjoints

For a symmetric positive-definite form on a finite-dimensional vector space over an ordered field,
an endomorphism composed with its adjoint has nonnegative trace, with equality only for zero. In
particular a skew-adjoint endomorphism has nonpositive trace of its square, with equality only for
zero. These trace criteria apply without choosing a norm or an inner-product-space structure.

## Main results

* `LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair`: `tr(A A^*)` is nonnegative.
* `LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair`: it vanishes exactly at `A = 0`.
* `LinearMap.BilinForm.trace_mul_self_nonpos_of_posDef`: the trace of the square of a
  skew-adjoint endomorphism is nonpositive.
* `LinearMap.BilinForm.trace_mul_self_eq_zero_iff_of_posDef`: equality holds exactly at zero.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Remark 12.2.14, for the skew-adjoint trace-square argument.
-/

public section

open Module

namespace LinearMap.BilinForm

section OrderedField

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem exists_positive_basis_adjoint (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B)
    (hpos : B.toQuadraticMap.PosDef) {A A' : Module.End F V} (hA : IsAdjointPair B B A A') :
    ∃ b : Basis (Fin (finrank F V)) F V,
      (∀ i, 0 < B (b i) (b i)) ∧
        ∀ i j, LinearMap.toMatrix b b A j i * B (b j) (b j) =
          B (b i) (b i) * LinearMap.toMatrix b b A' i j := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := exists_orthogonal_basis (isSymm_iff.mp hsymm)
  let d := fun i ↦ B (b i) (b i)
  let M := LinearMap.toMatrix b b A
  let M' := LinearMap.toMatrix b b A'
  have hd (i) : 0 < d i := by
    simpa only [d, LinearMap.BilinMap.toQuadraticMap_apply] using hpos (b i) (b.ne_zero i)
  have hJ : LinearMap.toMatrix₂ b b B = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [LinearMap.toMatrix₂_apply, Matrix.diagonal_apply_eq, d]
    · simp only [LinearMap.toMatrix₂_apply, Matrix.diagonal_apply_ne _ hij]
      exact (LinearMap.BilinForm.iIsOrtho_def.mp hb) i j hij
  have hB : Matrix.toLinearMap₂ b b (Matrix.diagonal d) = B := by
    rw [← hJ]
    exact Matrix.toLinearMap₂_toMatrix₂ b b B
  have hadj : Matrix.IsAdjointPair (Matrix.diagonal d) (Matrix.diagonal d) M M' := by
    apply (isAdjointPair_toLinearMap₂
      (b₁ := b) (b₂ := b) (J := Matrix.diagonal d) (J' := Matrix.diagonal d)
      (A := M) (A' := M')).mp
    simpa only [hB, M, M', Matrix.toLin_toMatrix] using hA
  rw [Matrix.IsAdjointPair] at hadj
  have hentry (i j) : M j i * d j = d i * M' i j := by
    have h := congrFun (congrFun hadj i) j
    simpa only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_mul] using h
  exact ⟨b, hd, hentry⟩

private theorem product_nonneg_and_eq_zero {ι : Type*} (d : ι → F) (M M' : Matrix ι ι F)
    (hd : ∀ i, 0 < d i) (hentry : ∀ i j, M j i * d j = d i * M' i j) (i j : ι) :
    0 ≤ M i j * M' j i ∧ (M i j * M' j i = 0 ↔ M i j = 0) := by
  have hw : d j * (M i j * M' j i) = d i * (M i j) ^ 2 := by
    calc
      _ = M i j * (d j * M' j i) := by ring
      _ = M i j * (M i j * d i) := by rw [hentry]
      _ = _ := by ring
  constructor
  · have hle : 0 ≤ d j * (M i j * M' j i) := by
      rw [hw]
      exact mul_nonneg (hd i).le (sq_nonneg _)
    exact nonneg_of_mul_nonneg_right hle (hd j)
  · constructor
    · intro h
      have hz : d i * (M i j) ^ 2 = 0 := hw.symm.trans (by rw [h, mul_zero])
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (hd i)))
    · intro h
      rw [h, zero_mul]

private theorem exists_matrix_trace_mul (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    {A A' : Module.End F V} (hA : IsAdjointPair B B A A') :
    ∃ M M' : Matrix (Fin (finrank F V)) (Fin (finrank F V)) F,
      LinearMap.trace F V (A * A') = ∑ i, ∑ j, M i j * M' j i ∧
      (∀ i j, 0 ≤ M i j * M' j i ∧ (M i j * M' j i = 0 ↔ M i j = 0)) ∧
      (M = 0 ↔ A = 0) := by
  classical
  obtain ⟨b, hd, hentry⟩ := exists_positive_basis_adjoint B hsymm hpos hA
  let M := LinearMap.toMatrix b b A
  let M' := LinearMap.toMatrix b b A'
  refine ⟨M, M', ?_, fun i j ↦ ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace F b (A * A'), LinearMap.toMatrix_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, M, M']
  · exact product_nonneg_and_eq_zero (fun i ↦ B (b i) (b i)) M M' hd hentry i j
  · exact ⟨fun h ↦ (LinearMap.toMatrix b b).injective (h.trans (map_zero _).symm),
      fun h ↦ (congrArg (LinearMap.toMatrix b b) h).trans (map_zero _)⟩

/-- For a symmetric positive-definite bilinear form, an endomorphism composed with its adjoint
has nonnegative trace. -/
theorem trace_mul_nonneg_of_isAdjointPair (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    {A A' : Module.End F V} (hA : IsAdjointPair B B A A') :
    0 ≤ LinearMap.trace F V (A * A') := by
  obtain ⟨M, M', htrace, hterm, _⟩ := exists_matrix_trace_mul B hsymm hpos hA
  rw [htrace]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hterm i j).1

/-- For a symmetric positive-definite bilinear form, an endomorphism composed with its adjoint
has trace zero exactly when the endomorphism is zero. -/
theorem trace_mul_eq_zero_iff_of_isAdjointPair (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    {A A' : Module.End F V} (hA : IsAdjointPair B B A A') :
    LinearMap.trace F V (A * A') = 0 ↔ A = 0 := by
  classical
  obtain ⟨M, M', htrace, hterm, hzero⟩ := exists_matrix_trace_mul B hsymm hpos hA
  rw [htrace, ← hzero]
  constructor
  · intro hsum
    have hrow (i) : (∑ j, M i j * M' j i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hterm i j).1)).mp hsum i (Finset.mem_univ i)
    ext i j
    exact (hterm i j).2.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ (hterm i j).1)).mp
        (hrow i) j (Finset.mem_univ j))
  · intro h
    simp only [h, Matrix.zero_apply, zero_mul, Finset.sum_const_zero]

/-- A skew-adjoint endomorphism for a symmetric positive-definite bilinear form has
nonpositive trace of its square. -/
theorem trace_mul_self_nonpos_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (A : Module.End F V) (hA : A ∈ B.skewAdjointSubmodule) :
    LinearMap.trace F V (A * A) ≤ 0 := by
  have h := trace_mul_nonneg_of_isAdjointPair B hsymm hpos
    (A := A) (A' := -A)
    ((LinearMap.mem_skewAdjointSubmodule A).mp hA)
  rwa [mul_neg, map_neg, neg_nonneg] at h

/-- A skew-adjoint endomorphism for a symmetric positive-definite bilinear form has
trace of its square equal to zero exactly when the endomorphism is zero. -/
theorem trace_mul_self_eq_zero_iff_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (A : Module.End F V) (hA : A ∈ B.skewAdjointSubmodule) :
    LinearMap.trace F V (A * A) = 0 ↔ A = 0 := by
  have h := trace_mul_eq_zero_iff_of_isAdjointPair B hsymm hpos
    (A := A) (A' := -A)
    ((LinearMap.mem_skewAdjointSubmodule A).mp hA)
  rwa [mul_neg, map_neg, neg_eq_zero] at h

end OrderedField

end LinearMap.BilinForm
