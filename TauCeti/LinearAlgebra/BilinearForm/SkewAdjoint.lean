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
# Trace of squares of skew-adjoint endomorphisms

For a symmetric positive-definite form on a finite-dimensional vector space over an ordered field, a
skew-adjoint endomorphism has nonpositive trace of its square, with equality only for zero.
These trace criteria apply without choosing a norm or an inner-product-space structure.

## Main results

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

private theorem exists_positive_basis_skew (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B)
    (hpos : B.toQuadraticMap.PosDef) (A : Module.End F V)
    (hA : A ∈ B.skewAdjointSubmodule) :
    ∃ b : Basis (Fin (finrank F V)) F V,
      (∀ i, 0 < B (b i) (b i)) ∧
        ∀ i j, LinearMap.toMatrix b b A j i * B (b j) (b j) =
          -(B (b i) (b i) * LinearMap.toMatrix b b A i j) := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := exists_orthogonal_basis (isSymm_iff.mp hsymm)
  let d := fun i ↦ B (b i) (b i)
  let M := LinearMap.toMatrix b b A
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
  have hskew : Matrix.IsAdjointPair (Matrix.diagonal d) (Matrix.diagonal d) M (-M) := by
    apply (isAdjointPair_toLinearMap₂
      (b₁ := b) (b₂ := b) (J := Matrix.diagonal d) (J' := Matrix.diagonal d)
      (A := M) (A' := -M)).mp
    simpa only [hB, M, map_neg, Matrix.toLin_toMatrix, LinearMap.IsSkewAdjoint,
      LinearMap.coe_neg] using
      (LinearMap.mem_skewAdjointSubmodule A).mp hA
  rw [Matrix.IsAdjointPair] at hskew
  have hentry (i j) : M j i * d j = -(d i * M i j) := by
    have h := congrFun (congrFun hskew i) j
    simpa only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_mul,
      Matrix.neg_apply, mul_neg] using h
  exact ⟨b, hd, hentry⟩

private theorem product_nonpos_and_eq_zero {ι : Type*} (d : ι → F) (M : Matrix ι ι F)
    (hd : ∀ i, 0 < d i) (hentry : ∀ i j, M j i * d j = -(d i * M i j)) (i j : ι) :
    M i j * M j i ≤ 0 ∧ (M i j * M j i = 0 ↔ M i j = 0) := by
  have hw : d j * (M i j * M j i) = -(d i * (M i j) ^ 2) := by
    calc
      _ = M i j * (M j i * d j) := by ring
      _ = M i j * -(d i * M i j) := by rw [hentry]
      _ = _ := by ring
  constructor
  · have hle : d j * (M i j * M j i) ≤ 0 := by
      rw [hw]
      exact neg_nonpos.mpr (mul_nonneg (hd i).le (sq_nonneg _))
    by_contra h
    exact (not_lt_of_ge hle) (mul_pos (hd j) (lt_of_not_ge h))
  · constructor
    · intro h
      have hz : -(d i * (M i j) ^ 2) = 0 :=
        hw.symm.trans (by rw [h, mul_zero])
      have hs : (M i j) ^ 2 = 0 :=
        (mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_left (ne_of_gt (hd i))
      exact sq_eq_zero_iff.mp hs
    · intro h
      rw [h, zero_mul]

private theorem exists_matrix_trace_mul_self (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (A : Module.End F V) (hA : A ∈ B.skewAdjointSubmodule) :
    ∃ M : Matrix (Fin (finrank F V)) (Fin (finrank F V)) F,
      LinearMap.trace F V (A * A) = ∑ i, ∑ j, M i j * M j i ∧
      (∀ i j, M i j * M j i ≤ 0 ∧ (M i j * M j i = 0 ↔ M i j = 0)) ∧
      (M = 0 ↔ A = 0) := by
  classical
  obtain ⟨b, hd, hentry⟩ := exists_positive_basis_skew B hsymm hpos A hA
  let M := LinearMap.toMatrix b b A
  refine ⟨M, ?_, fun i j ↦ ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace F b (A * A), LinearMap.toMatrix_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, M]
  · exact product_nonpos_and_eq_zero (fun i ↦ B (b i) (b i)) M hd hentry i j
  · exact ⟨fun h ↦ (LinearMap.toMatrix b b).injective (h.trans (map_zero _).symm),
      fun h ↦ (congrArg (LinearMap.toMatrix b b) h).trans (map_zero _)⟩

/-- A skew-adjoint endomorphism for a symmetric positive-definite bilinear form has
nonpositive trace of its square. -/
theorem trace_mul_self_nonpos_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (A : Module.End F V) (hA : A ∈ B.skewAdjointSubmodule) :
    LinearMap.trace F V (A * A) ≤ 0 := by
  obtain ⟨M, htrace, hterm, _⟩ := exists_matrix_trace_mul_self B hsymm hpos A hA
  rw [htrace]
  exact Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j _ ↦ (hterm i j).1

/-- A skew-adjoint endomorphism for a symmetric positive-definite bilinear form has
trace of its square equal to zero exactly when the endomorphism is zero. -/
theorem trace_mul_self_eq_zero_iff_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (A : Module.End F V) (hA : A ∈ B.skewAdjointSubmodule) :
    LinearMap.trace F V (A * A) = 0 ↔ A = 0 := by
  classical
  obtain ⟨M, htrace, hterm, hzero⟩ := exists_matrix_trace_mul_self B hsymm hpos A hA
  rw [htrace, ← hzero]
  constructor
  · intro hsum
    have hrow (i) : (∑ j, M i j * M j i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos
        (fun i _ ↦ Finset.sum_nonpos fun j _ ↦ (hterm i j).1)).mp hsum i (Finset.mem_univ i)
    ext i j
    exact (hterm i j).2.mp
      ((Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ (hterm i j).1)).mp
        (hrow i) j (Finset.mem_univ j))
  · rintro rfl
    simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero]

end OrderedField

end LinearMap.BilinForm
