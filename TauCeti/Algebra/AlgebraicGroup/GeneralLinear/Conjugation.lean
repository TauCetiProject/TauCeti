/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# Conjugation of `GLₙ` by a constant matrix, in coordinates

An invertible matrix `P` over the base ring `R` is an `R`-valued point of `GLₙ`, so inner
conjugation by it is an automorphism of the affine group scheme `GLₙ` over `R`, and hence an
automorphism of the coordinate Hopf algebra `O(GLₙ/R)`. This file names that coordinate
automorphism and records what it does on algebra-valued points: precomposing a point with it
conjugates the corresponding invertible matrix by the image of `P`,

```text
g ↦ P g P⁻¹.
```

This is the form in which a comparison of two closed subgroup schemes of `GLₙ` related by a
change of basis is stated: a Hopf ideal is carried to another one exactly when the coordinate
automorphism carries it there, and on points that is conjugation by the change-of-basis matrix.

## Main declarations

* `TauCeti.GeneralLinear.conjCoordinateIso`: the coordinate Hopf-algebra automorphism of `GLₙ`
  induced by conjugation by a constant invertible matrix.

## Main results

* `TauCeti.GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso` and
  `TauCeti.GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso`: on algebra-valued points
  the coordinate automorphism is conjugation by the base-changed matrix.
* `TauCeti.GeneralLinear.conjCoordinateIso_inv`: conjugation by the inverse matrix is the inverse
  coordinate automorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The coordinate Hopf-algebra automorphism of `GLₙ` over `R` induced by conjugation by a
constant invertible matrix `P`. -/
noncomputable def conjCoordinateIso (P : Matrix.GeneralLinearGroup (Fin n) R) :
    coordinateHopfAlgebra R n ≅ coordinateHopfAlgebra R n :=
  CommHopfAlgCat.innerConjugationIso (coordinateHopfAlgebra R n)
    ((pointsMulEquiv (R := R) (A := R) n).symm P)

/-- The `R`-valued point underlying a constant matrix, extended to an `R`-algebra `A`, is the
image of that matrix over `A`. -/
private theorem pointsMulEquiv_extendPoint_symm (P : Matrix.GeneralLinearGroup (Fin n) R)
    (A : CommAlgCat.{v} R) :
    pointsMulEquiv n
        (HopfAlgebra.extendPoint (coordinateHopfAlgebra R n) A
          ((pointsMulEquiv (R := R) (A := R) n).symm P)) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) P := by
  rw [← HopfAlgebra.mapValue_extendPoint _ (A := CommAlgCat.of R R) (Algebra.ofId R A),
    HopfAlgebra.extendPoint_self, pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply,
    Algebra.toRingHom_ofId]

/-- **On algebra-valued points, the coordinate automorphism of conjugation by `P` is conjugation
by the image of `P`.** -/
theorem pointsMulEquiv_mapPointsFunctor_conjCoordinateIso
    (P : Matrix.GeneralLinearGroup (Fin n) R) (A : CommAlgCat.{v} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    pointsMulEquiv n
        ((CommHopfAlgCat.mapPointsFunctor (conjCoordinateIso P).hom).app A f) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) P * pointsMulEquiv n f *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ := by
  rw [conjCoordinateIso, CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom,
    HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv,
    pointsMulEquiv_extendPoint_symm]

/-- **Precomposing a point with the coordinate automorphism of conjugation by `P` conjugates its
matrix by the image of `P`**, over a value ring in any universe. -/
theorem pointsMulEquiv_toConv_comp_conjCoordinateIso
    (P : Matrix.GeneralLinearGroup (Fin n) R) (A : Type v) [CommRing A] [Algebra R A]
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n
        (toConv (f.ofConv.comp
          ((conjCoordinateIso P).hom.hom : coordinateHopfAlgebra R n →ₐ[R]
            coordinateHopfAlgebra R n))) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) P * pointsMulEquiv n f *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ := by
  simpa only [CommHopfAlgCat.mapPointsFunctor_app_apply] using
    pointsMulEquiv_mapPointsFunctor_conjCoordinateIso P (CommAlgCat.of R A) f

/-- Conjugation by the inverse matrix is the inverse coordinate automorphism. -/
@[simp]
theorem conjCoordinateIso_inv (P : Matrix.GeneralLinearGroup (Fin n) R) :
    conjCoordinateIso P⁻¹ = (conjCoordinateIso P).symm := by
  rw [conjCoordinateIso, conjCoordinateIso, map_inv,
    CommHopfAlgCat.innerConjugationIso_inv_point]

end TauCeti.GeneralLinear
