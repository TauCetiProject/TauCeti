/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Cauchy interlacing for principal submatrices

Let `A` be a Hermitian matrix indexed by a finite type `n`, and let `B = A.submatrix f f` be the
principal submatrix selected by an embedding `f : m ↪ n`. With the decreasing enumeration
`Matrix.IsHermitian.eigenvalues₀` of the eigenvalues, repeated by multiplicity, Cauchy's
interlacing theorem states
`λ_{i + (|n| - |m|)}(A) ≤ λᵢ(B) ≤ λᵢ(A)`
for every `i < |m|`.

Both inequalities are first proved for symmetric operators `S` on `F` and `T` on `E` related by a
linear isometry `ι : F → E` with `⟪S x, x⟫ = ⟪T (ι x), ι x⟫`. The matrix statements follow by
extending vectors by zero along `f`, which identifies the Rayleigh form of `B` with that of `A`
on the range of the extension. The two bounds are the two directions of the Courant–Fischer
theorem in `TauCeti.Analysis.InnerProductSpace.CourantFischer`: the upper bound transports a
subspace of the smaller space into the larger one, and the lower bound pulls a subspace of the
larger space back, with a dimension count.

## Main results

* `LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry` and
  `LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry'` in
  `TauCeti.Analysis.InnerProductSpace.CourantFischer`: the operator-level bounds.
* `Matrix.IsHermitian.eigenvalues₀_submatrix_le`: `λᵢ(B) ≤ λᵢ(A)`.
* `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_submatrix`:
  `λ_{i + (|n| - |m|)}(A) ≤ λᵢ(B)`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 4.3.28 (Cauchy interlacing theorem).
* R. Bhatia, *Matrix Analysis*, Springer (1997), Corollary III.1.5.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix n n 𝕜}

/-- **Cauchy interlacing, upper bound.** Each sorted eigenvalue of a principal submatrix of a
Hermitian matrix is at most the sorted eigenvalue of the same index of the full matrix. -/
theorem eigenvalues₀_submatrix_le (hA : A.IsHermitian) (f : m ↪ n) (i : Fin (Fintype.card m)) :
    (hA.submatrix f).eigenvalues₀ i ≤
      hA.eigenvalues₀ (Fin.castLE (Fintype.card_le_of_embedding f) i) :=
  LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.submatrix f)) finrank_euclideanSpace
    finrank_euclideanSpace (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f)
    (fun x ↦ (Matrix.inner_toEuclideanLin_piLpExtendByZero A f x).symm)
    (Fintype.card_le_of_embedding f) i

/-- **Cauchy interlacing, lower bound.** The sorted eigenvalue of index `i + (|n| - |m|)` of a
Hermitian matrix is at most the `i`-th sorted eigenvalue of any principal submatrix of size
`|m|`. -/
theorem eigenvalues₀_le_eigenvalues₀_submatrix (hA : A.IsHermitian) (f : m ↪ n)
    (i : Fin (Fintype.card m)) :
    hA.eigenvalues₀ (Fin.cast (Nat.add_sub_of_le (Fintype.card_le_of_embedding f))
        (i.addNat (Fintype.card n - Fintype.card m))) ≤ (hA.submatrix f).eigenvalues₀ i :=
  LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry'
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.submatrix f)) finrank_euclideanSpace
    finrank_euclideanSpace (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f)
    (fun x ↦ (Matrix.inner_toEuclideanLin_piLpExtendByZero A f x).symm)
    (Fintype.card_le_of_embedding f) i

end Matrix.IsHermitian
