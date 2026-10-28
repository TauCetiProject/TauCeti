/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.UpperTriangular
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda

/-!
# The represented diagonal Levi projection of the special-linear Borel

The diagonal projection of upper-triangular determinant-one matrices is natural in the value
algebra, so the fully faithful functor of points represents it by a coordinate Hopf-algebra
endomorphism. This endomorphism is idempotent. Its image on every algebra-valued point group
consists exactly of diagonal matrices, and its scheme-theoretic kernel has exactly the
upper-unitriangular matrices as its algebra-valued points.

Together with `existsUnique_unipotent_mul_diagonal`, this gives the diagonal Levi projection
and the unique unipotent-times-diagonal factorization over arbitrary commutative rings. In
particular the kernel computation retains infinitesimal points; it does not rely on testing
only field-valued points. Identifying this kernel with the unipotent radical requires its
geometric properties in addition to this projection.

The construction uses `CommHopfAlgCat.homOfPointsMap` and the existing natural equivalence
`SpecialLinear.UpperTriangular.pointsMulEquiv`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, §6.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

universe u v w

noncomputable section

variable (R : Type u) [CommRing R] (n : ℕ)

private def diagonalProjectionPointsHom (A : Type v) [CommRing A] [Algebra R A] :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) →*
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) :=
  (pointsMulEquiv R n).symm.toMonoidHom.comp
    (diagonalProjection.comp (pointsMulEquiv R n).toMonoidHom)

private theorem pointsMulEquiv_diagonalProjectionPointsHom
    {A : Type v} [CommRing A] [Algebra R A]
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    pointsMulEquiv R n (A := A) (diagonalProjectionPointsHom R n A g) =
      diagonalProjection (pointsMulEquiv R n (A := A) g) :=
  (pointsMulEquiv R n).apply_symm_apply _

private theorem diagonalProjectionPointsHom_mapValue
    {A : Type v} [CommRing A] [Algebra R A]
    {B : Type w} [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    AlgHom.mapValue f (diagonalProjectionPointsHom R n A g) =
      diagonalProjectionPointsHom R n B (AlgHom.mapValue f g) := by
  apply (pointsMulEquiv R n).injective
  apply Subtype.ext
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_diagonalProjectionPointsHom,
    pointsMulEquiv_diagonalProjectionPointsHom, map_diagonalProjection]
  have h := pointsMulEquiv_mapValue R n f g
  ext i j
  simp only [diagonalProjection_coe]
  rw [h]

private def diagonalProjectionPointsMap :
    HopfAlgebra.pointsFunctor.{u, u, u} (R := R) (H := coordinateHopfAlgebra R n) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n) where
  app A := GrpCat.ofHom (diagonalProjectionPointsHom R n A)
  naturality {A B} f := by
    ext g
    exact (diagonalProjectionPointsHom_mapValue R n f.hom g).symm

/-- The coordinate Hopf-algebra endomorphism representing diagonal Levi projection of the
upper-triangular subgroup of `SLₙ`. Its direction is opposite to the group-scheme projection. -/
def diagonalProjectionCoordinateMap : coordinateHopfAlgebra R n ⟶ coordinateHopfAlgebra R n :=
  CommHopfAlgCat.homOfPointsMap (diagonalProjectionPointsMap R n)

/-- On algebra-valued points, the represented Levi projection takes the diagonal matrix.
This formula holds in every value universe and over nonreduced coefficient algebras. -/
@[simp↓ high]
theorem pointsMulEquiv_diagonalProjectionCoordinateMap
    {A : Type v} [CommRing A] [Algebra R A]
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    pointsMulEquiv R n (A := A)
        (toConv (g.ofConv.comp (diagonalProjectionCoordinateMap R n).hom)) =
      diagonalProjection (pointsMulEquiv R n (A := A) g) := by
  have hgeneric := congrArg (fun α ↦ α.app (CommAlgCat.of R (coordinateHopfAlgebra R n))
      (toConv (AlgHom.id R (coordinateHopfAlgebra R n))))
    (CommHopfAlgCat.mapPointsFunctor_homOfPointsMap (diagonalProjectionPointsMap R n))
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hgeneric
  have hpoint : toConv (g.ofConv.comp (diagonalProjectionCoordinateMap R n).hom) =
      diagonalProjectionPointsHom R n A g := by
    calc
      _ = AlgHom.mapValue g.ofConv
          (toConv ((diagonalProjectionCoordinateMap R n).hom.toAlgHom)) := by
        rw [AlgHom.mapValue_apply]
      _ = AlgHom.mapValue g.ofConv
          (diagonalProjectionPointsHom R n (coordinateHopfAlgebra R n)
            (toConv (AlgHom.id R (coordinateHopfAlgebra R n)))) := by
        exact congrArg (AlgHom.mapValue g.ofConv) hgeneric
      _ = _ := by
        rw [diagonalProjectionPointsHom_mapValue]
        simp only [AlgHom.mapValue_apply, AlgHom.comp_id, toConv_ofConv]
  rw [hpoint, pointsMulEquiv_diagonalProjectionPointsHom]

/-- The represented diagonal Levi projection is idempotent. -/
@[simp]
theorem diagonalProjectionCoordinateMap_comp_self :
    diagonalProjectionCoordinateMap R n ≫ diagonalProjectionCoordinateMap R n =
      diagonalProjectionCoordinateMap R n := by
  rw [diagonalProjectionCoordinateMap, ← CommHopfAlgCat.homOfPointsMap_comp]
  congr 1
  ext A g
  rcases A with ⟨A⟩
  -- Extensionality gives the bundled functor carrier; the pointwise API uses convolution points.
  change HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) at g
  apply (pointsMulEquiv R n (A := A)).injective
  have h : pointsMulEquiv R n (A := A)
      (diagonalProjectionPointsHom R n A (diagonalProjectionPointsHom R n A g)) =
        pointsMulEquiv R n (A := A) (diagonalProjectionPointsHom R n A g) := by
    calc
      _ = diagonalProjection (pointsMulEquiv R n (A := A)
          (diagonalProjectionPointsHom R n A g)) :=
        pointsMulEquiv_diagonalProjectionPointsHom R n _
      _ = diagonalProjection (diagonalProjection (pointsMulEquiv R n (A := A) g)) :=
        congrArg diagonalProjection (pointsMulEquiv_diagonalProjectionPointsHom R n g)
      _ = diagonalProjection (pointsMulEquiv R n (A := A) g) := diagonalProjection_idempotent _
      _ = _ := (pointsMulEquiv_diagonalProjectionPointsHom R n g).symm
  exact h

/-- The scheme-theoretic kernel of diagonal Levi projection is the upper-unitriangular
subgroup, tested on every commutative value algebra. -/
@[simp↓]
theorem mem_diagonalProjection_kernelPoints_iff
    {A : Type v} [CommRing A] [Algebra R A]
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n)
        (CommHopfAlgCat.kernelHopfIdeal (diagonalProjectionCoordinateMap R n))
        (CommAlgCat.of R A) ↔
      Matrix.SpecialLinearGroup.toGL (pointsMulEquiv R n (A := A) g).1 ∈
        upperUnitriangularGroup (Fin n) A := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff]
  rw [← (pointsMulEquiv R n).map_eq_one_iff,
    pointsMulEquiv_diagonalProjectionCoordinateMap, diagonalProjection_eq_one_iff]

end

end TauCeti.SpecialLinear.UpperTriangular
