/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix inverses under homomorphisms and changes of representation

Applying a ring homomorphism `f : R →+* S` entrywise commutes with taking the inverse of a square
matrix, provided `f` is a local homomorphism (`Matrix.map_nonsing_inv`). The inverse
`A⁻¹ = Ring.inverse (det A) • adjugate A` is built from the determinant and the adjugate, which
commute with every ring homomorphism (`RingHom.map_det`, `RingHom.map_adjugate`), and a local
homomorphism commutes with `Ring.inverse` (`map_ringInverse`).

Locality is needed: `ℤ →+* ℚ` is not local, and the `1 × 1` matrix `2` over `ℤ` has inverse `0`,
while its image in `ℚ` has inverse `1 / 2`. Every ring homomorphism from a field to a nontrivial
ring is local, so the statement applies, for instance, to the casts `ℚ → ℝ` and `ℝ → ℂ`: an
inverse computed over `ℚ` is the inverse over `ℝ`.

`Matrix.inv_submatrix_mul_row_eq_single` normalizes the rows of a matrix whose columns off a pivot
set vanish to coordinate vectors, by the inverse of its pivot submatrix.

`LinearMap.toMatrix_ringInverse` identifies the matrix of an endomorphism's ring inverse.
-/

public section

namespace Matrix

variable {n R S F : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  [FunLike F R S] [RingHomClass F R S]

/-- A local ring homomorphism applied entrywise commutes with the inverse of a square matrix. -/
@[simp]
theorem map_nonsing_inv (f : F) [IsLocalHom f] (A : Matrix n n R) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : f A.det = (A.map f).det := RingHom.map_det (f : R →+* S) A
  have hadj : A.adjugate.map f = (A.map f).adjugate := RingHom.map_adjugate (f : R →+* S) A
  rw [inv_def, inv_def, ← hdet, ← hadj, ← map_ringInverse f]
  ext i j
  simp

/-- If the column change `Q` kills `x` off the pivot columns `e`, then normalizing by the inverse of
the pivot matrix turns the rows of `x * Q` into coordinate vectors. -/
theorem inv_submatrix_mul_row_eq_single {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {p : ℕ}
    {x : Matrix (Fin p) ι K} {e : Fin p ↪ ι} {Q : Matrix ι ι K} (he : (x.submatrix id e).det ≠ 0)
    (hred : ∀ i j, (x * Q) i j = if j ∈ Set.range e then x i j else 0) :
    ((x.submatrix id e)⁻¹ * (x * Q)).row = fun i ↦ Pi.single (e i) 1 := by
  set P := x.submatrix id e
  ext i j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨b, rfl⟩ := hj
    have h := congrArg (fun M : Matrix (Fin p) (Fin p) K ↦ M i b)
      (Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr he))
    simpa [P, Matrix.mul_apply, hred, Pi.single_apply,
      e.injective.eq_iff, Matrix.one_apply, eq_comm] using h
  · have hz : ∀ b, e b ≠ j := fun b h ↦ hj ⟨b, h⟩
    simp [Matrix.mul_apply, hred, hj, hz, Ne.symm]

end Matrix

namespace LinearMap

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommMonoid M] [Module R M]

/-- The matrix of the ring inverse of an endomorphism is the inverse of its matrix. -/
theorem toMatrix_ringInverse (b : Module.Basis ι R M) (A : M →ₗ[R] M) :
    toMatrix b b (Ring.inverse A) = (toMatrix b b A)⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  simpa only [toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply] using
    map_ringInverse (toMatrixAlgEquiv b) A

end LinearMap
