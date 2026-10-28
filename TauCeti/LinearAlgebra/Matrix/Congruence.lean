/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Traces and determinant pencils under rectangular congruence

For a rectangular matrix `M`, congruence `A ↦ M * A * Mᵀ` can be moved across a trace pairing
or a determinant pencil `det (1 + c • (B * _))` by congruating the test matrix `B` with the
transpose instead. These identities transport Wishart trace transforms along congruence. The file
also records the scalar regrouping that produces a congruence in the first place: expanding the
two weights of a doubly indexed family along the rows of `M` replaces the weight matrix by its
congruate.

## Main results

* `Matrix.trace_mul_congruence` — `trace (B * (M * A * Mᵀ)) = trace ((Mᵀ * B * M) * A)`.
* `Matrix.sum_sum_smul_congruence` — expanding the weights of `∑ x y, A x y • T x y` along the
  rows of `M` congruates `A`.
* `Matrix.det_one_add_smul_transpose_mul_mul`,
  `Matrix.det_one_sub_smul_transpose_mul_mul` — the corresponding determinant pencil identities,
  instances of the Weinstein--Aronszajn identity `Matrix.det_one_add_mul_comm`.
* `Matrix.submatrix_one_mul_mul_submatrix_one` — congruence by a selection matrix is the
  corresponding submatrix.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2–3.
-/

public section

namespace Matrix

/-- Moving a rectangular congruence across a trace pairing transposes the congruence matrix.
No symmetry hypotheses on `A` or `B` are needed. -/
theorem trace_mul_congruence {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalCommSemiring R]
    (B : Matrix m m R) (M : Matrix m n R) (A : Matrix n n R) :
    (B * (M * A * Mᵀ)).trace = ((Mᵀ * B * M) * A).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * M * A) Mᵀ

/-- The Weinstein--Aronszajn identity in the form used by a rectangular congruence: the
determinant pencil can be computed either before or after applying the congruence. -/
theorem det_one_add_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + c • (B * (M * A * Mᵀ))) := by
  calc
    det (1 + c • ((Mᵀ * B * M) * A)) = det (1 + Mᵀ * (c • (B * M * A))) := by
      simp only [Matrix.mul_assoc, Matrix.mul_smul]
    _ = det (1 + (c • (B * M * A)) * Mᵀ) :=
      Matrix.det_one_add_mul_comm Mᵀ (c • (B * M * A))
    _ = det (1 + c • (B * (M * A * Mᵀ))) := by
      simp only [Matrix.smul_mul, Matrix.mul_assoc]

/-- The subtractive form of `Matrix.det_one_add_smul_transpose_mul_mul`. This is the form of the
determinant pencil occurring in Wishart moment-generating functions. -/
theorem det_one_sub_smul_transpose_mul_mul {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (c : R) (B : Matrix m m R)
    (M : Matrix m n R) (A : Matrix n n R) :
    det (1 - c • ((Mᵀ * B * M) * A)) = det (1 - c • (B * (M * A * Mᵀ))) := by
  simpa only [sub_eq_add_neg, neg_smul] using
    det_one_add_smul_transpose_mul_mul (-c) B M A

/-- **Congruence by a selection matrix reads off a submatrix.** The matrix
`(1 : Matrix n n R).submatrix f id` keeps the rows named by `f` and its transpose
`(1 : Matrix n n R).submatrix id f` keeps the columns, so congruating with it keeps exactly the
rows and columns named by `f`. -/
@[simp]
theorem submatrix_one_mul_mul_submatrix_one {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] (f : m → n) (A : Matrix n n R) :
    (1 : Matrix n n R).submatrix f id * A * (1 : Matrix n n R).submatrix id f =
      A.submatrix f f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- **Congruence from a double expansion of the weights.** Pushing a matrix `M` through both
indices of a doubly indexed family `T` in a module turns the weight matrix `A` into the congruate
`M * A * Mᵀ`. The family is arbitrary, so the regrouping serves both a bivector in a tensor square
and two slots of a larger tensor power, where those two slots cannot be split off as a tensor
square. -/
theorem sum_sum_smul_congruence {m n R P : Type*} [Fintype m] [Fintype n] [CommSemiring R]
    [AddCommMonoid P] [Module R P] (M : Matrix m n R) (A : Matrix n n R) (T : m → m → P) :
    ∑ x : n, ∑ y : n, A x y • ∑ a : m, ∑ b : m, (M a x * M b y) • T a b =
      ∑ a : m, ∑ b : m, (M * A * Mᵀ) a b • T a b := by
  have hcoef : ∀ a b : m, ∑ x : n, ∑ y : n, A x y * (M a x * M b y) = (M * A * Mᵀ) a b := by
    intro a b
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  calc ∑ x : n, ∑ y : n, A x y • ∑ a : m, ∑ b : m, (M a x * M b y) • T a b
      = ∑ x : n, ∑ y : n, ∑ a : m, ∑ b : m, (A x y * (M a x * M b y)) • T a b := by
        simp only [Finset.smul_sum, smul_smul]
    -- move the two outer sums past the two inner ones, one adjacent swap at a time
    _ = ∑ x : n, ∑ a : m, ∑ y : n, ∑ b : m, (A x y * (M a x * M b y)) • T a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : m, ∑ x : n, ∑ y : n, ∑ b : m, (A x y * (M a x * M b y)) • T a b := Finset.sum_comm
    _ = ∑ a : m, ∑ x : n, ∑ b : m, ∑ y : n, (A x y * (M a x * M b y)) • T a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : m, ∑ b : m, ∑ x : n, ∑ y : n, (A x y * (M a x * M b y)) • T a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : m, ∑ b : m, (M * A * Mᵀ) a b • T a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [← Finset.sum_smul]
        rw [hcoef a b]

end Matrix
