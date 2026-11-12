/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

/-!
# Diagonal Levi projection for upper-triangular special linear matrices

Taking the diagonal of an upper-triangular determinant-one matrix preserves its determinant.
It therefore defines an idempotent group endomorphism of the special-linear Borel over any
commutative ring. Its fixed points are the diagonal matrices and its kernel consists of
upper-unitriangular matrices. Every element factors uniquely as a kernel element followed by
a fixed point. Naturality in the coefficient ring lets this projection be represented by a
morphism of affine group schemes.

The construction restricts `UpperTriangularGroup.diag` and
`UpperTriangularGroup.diagonalHom` to determinant one.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, §6.3.
-/

public section

namespace TauCeti.SpecialLinear.UpperTriangular

open Matrix

variable {m : Type*} [Fintype m] [LinearOrder m] {A : Type*} [CommRing A]

/-- The diagonal Levi projection of the upper-triangular special linear group. -/
def diagonalProjection :
    (upperTriangularGroup m A).comap SpecialLinearGroup.toGL →*
      (upperTriangularGroup m A).comap SpecialLinearGroup.toGL where
  toFun g :=
    ⟨⟨Matrix.diagonal fun i ↦ (g.1 : Matrix m m A) i i, by
      rw [Matrix.det_diagonal, ← Matrix.det_of_isUpperTriangular
        (UpperTriangularGroup.mem_comap_toGL_iff.mp g.2)]
      exact g.1.property⟩,
      UpperTriangularGroup.mem_comap_toGL_iff.mpr (Matrix.blockTriangular_diagonal _)⟩
  map_one' := by ext i j; simp
  map_mul' g h := by
    ext i j
    -- Unpack the determinant-one and subgroup carriers before computing matrix multiplication.
    change Matrix.diagonal (fun k ↦ ((g.1 : Matrix m m A) * h.1) k k) i j =
      (Matrix.diagonal (fun k ↦ (g.1 : Matrix m m A) k k) *
        Matrix.diagonal (fun k ↦ (h.1 : Matrix m m A) k k)) i j
    rw [Matrix.diagonal_mul_diagonal]
    congr 2
    funext k
    exact Matrix.mul_apply_diag_of_isUpperTriangular
      (UpperTriangularGroup.mem_comap_toGL_iff.mp g.2)
      (UpperTriangularGroup.mem_comap_toGL_iff.mp h.2) k

/-- The projection retains precisely the diagonal entries of the original matrix. -/
@[simp]
theorem diagonalProjection_coe
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    ((diagonalProjection g).1 : Matrix m m A) =
      Matrix.diagonal (fun i ↦ (g.1 : Matrix m m A) i i) := (rfl)

/-- Diagonal projection is idempotent. -/
@[simp]
theorem diagonalProjection_idempotent
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    diagonalProjection (diagonalProjection g) = diagonalProjection g := by
  ext i j
  simp

/-- The fixed points of diagonal projection are exactly the diagonal matrices. -/
@[simp]
theorem diagonalProjection_eq_self_iff
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    diagonalProjection g = g ↔ (g.1 : Matrix m m A).IsDiag := by
  constructor
  · intro h
    have hmat := congrArg (fun x : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL ↦
      (x.1 : Matrix m m A)) h
    rw [diagonalProjection_coe] at hmat
    exact hmat ▸ Matrix.isDiag_diagonal _
  · intro h
    apply Subtype.ext
    apply SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun h.diagonal_diag i) j

/-- The kernel of diagonal projection consists exactly of upper-unitriangular matrices. -/
@[simp]
theorem diagonalProjection_eq_one_iff
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    diagonalProjection g = 1 ↔
      SpecialLinearGroup.toGL g.1 ∈ upperUnitriangularGroup m A := by
  rw [UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def]
  constructor
  · intro h
    refine ⟨UpperTriangularGroup.mem_comap_toGL_iff.mp g.2, fun i ↦ ?_⟩
    have hi := congrArg (fun x : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL ↦
      (x.1 : Matrix m m A) i i) h
    simpa using hi
  · rintro ⟨_, h⟩
    ext i j
    simpa using congrFun (congrFun
      (congrArg Matrix.diagonal (funext h)) i) j

/-- Diagonal projection commutes with every homomorphism of coefficient rings. -/
@[simp]
theorem map_diagonalProjection {B : Type*} [CommRing B] (f : A →+* B)
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    SpecialLinearGroup.map f (diagonalProjection g).1 =
      (diagonalProjection ⟨SpecialLinearGroup.map f g.1,
        UpperTriangularGroup.mem_comap_toGL_iff.mpr
          ((UpperTriangularGroup.mem_comap_toGL_iff.mp g.2).map f)⟩).1 := by
  ext i j
  simp [diagonalProjection_coe, Matrix.diagonal_apply, apply_ite f]

/-- Every upper-triangular determinant-one matrix factors uniquely into an upper-unitriangular
matrix followed by a diagonal determinant-one matrix. -/
theorem existsUnique_unipotent_mul_diagonal
    (g : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL) :
    ∃! p : (upperTriangularGroup m A).comap SpecialLinearGroup.toGL ×
        (upperTriangularGroup m A).comap SpecialLinearGroup.toGL,
      SpecialLinearGroup.toGL p.1.1 ∈ upperUnitriangularGroup m A ∧
        (p.2.1 : Matrix m m A).IsDiag ∧ p.1 * p.2 = g := by
  refine ⟨(g * (diagonalProjection g)⁻¹, diagonalProjection g), ?_, ?_⟩
  · refine ⟨(diagonalProjection_eq_one_iff _).mp ?_,
      (diagonalProjection_eq_self_iff _).mp (diagonalProjection_idempotent g), ?_⟩
    · simp
    · simp
  · rintro ⟨v, d⟩ ⟨hv, hd, hprod⟩
    have hdiag : diagonalProjection g = d := by
      rw [← hprod, map_mul, (diagonalProjection_eq_one_iff v).mpr hv,
        (diagonalProjection_eq_self_iff d).mpr hd, one_mul]
    apply Prod.ext
    · exact (eq_mul_inv_iff_mul_eq.mpr hprod).trans (congrArg (g * ·⁻¹) hdiag.symm)
    · exact hdiag.symm

end TauCeti.SpecialLinear.UpperTriangular
