/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic

/-!
# Inverse transpose on the general linear group scheme

Inverse transpose `g ↦ (g⁻¹)ᵀ` is an automorphism of `GL_n(A)` for every commutative algebra `A`
over the base ring `R`, natural in `A`. It is therefore an automorphism of the affine group scheme
`GLₙ` over `R`, and so an automorphism of the coordinate Hopf algebra `O(GLₙ/R)`. This file names
that coordinate automorphism, records what it does on algebra-valued points, and shows that it is
an involution whose fixed points are the orthogonal group.

Over `ℝ`, this is the standard Cartan involution of `GLₙ`: its real fixed points form the
orthogonal group, and its twisted real form is the unitary group.

## Main declarations

* `TauCeti.GeneralLinear.inverseTransposeCoordinateIso`: the coordinate Hopf-algebra automorphism
  of `GLₙ` induced by inverse transpose.

## Main results

* `TauCeti.GeneralLinear.pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso`: precomposing a
  point with it applies inverse transpose to the corresponding invertible matrix.
* `TauCeti.GeneralLinear.inverseTransposeCoordinateIso_hom_comp_self`: it is an involution.
* `TauCeti.GeneralLinear.toConv_comp_inverseTransposeCoordinateIso_eq_self_iff`: its fixed
  points are the orthogonal matrices.

## References

* J. S. Milne, *Introduction to Shimura varieties*, notes, version of 16 September 2017, §1,
  Example 1.17(b), p. 15.

The passage from a natural automorphism of the functor of points to a coordinate automorphism
follows `TauCeti.GeneralLinear.typeAGraphCoordinateIso` and
`TauCeti.HopfAlgebra.innerConjugationPointNatIso`, through `TauCeti.CommHopfAlgCat.homOfPointsMap`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Inverse transpose on the points of `GLₙ` with values in a fixed algebra. -/
private noncomputable def inverseTransposePointsMulEquiv (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A ≃*
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A :=
  ((pointsMulEquiv (R := R) (A := A) n).trans Matrix.GeneralLinearGroup.inverseTranspose).trans
    (pointsMulEquiv (R := R) (A := A) n).symm

private theorem pointsMulEquiv_inverseTransposePointsMulEquiv (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    pointsMulEquiv n (inverseTransposePointsMulEquiv R n A f) =
      Matrix.GeneralLinearGroup.inverseTranspose (pointsMulEquiv n f) := by
  rw [inverseTransposePointsMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact (pointsMulEquiv (R := R) (A := A) n).apply_symm_apply _

/-- Inverse transpose on the points of `GLₙ` is an involution. -/
private theorem inverseTransposePointsMulEquiv_apply_apply (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    inverseTransposePointsMulEquiv R n A (inverseTransposePointsMulEquiv R n A f) = f := by
  apply (pointsMulEquiv (R := R) (A := A) n).injective
  rw [pointsMulEquiv_inverseTransposePointsMulEquiv, pointsMulEquiv_inverseTransposePointsMulEquiv,
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]

/-- Inverse transpose, naturally on the functor of points of `GLₙ`. -/
private noncomputable def inverseTransposePointsNatIso :
    HopfAlgebra.pointsFunctor.{u, u, u} (R := R) (H := coordinateHopfAlgebra R n) ≅
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n) :=
  NatIso.ofComponents (fun A ↦
    MulEquiv.toGrpIso
      (X := (HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n)).obj A)
      (inverseTransposePointsMulEquiv R n A))
    fun {A B} φ ↦ by
    -- Normalize the functor objects in the induced group instances as well as in the maps.
    dsimp +instances only [HopfAlgebra.pointsFunctor_obj, HopfAlgebra.pointsFunctor_map]
    apply GrpCat.ext
    intro (x : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A)
    rw [GrpCat.comp_apply, GrpCat.comp_apply, MulEquiv.toGrpIso_hom, MulEquiv.toGrpIso_hom]
    simp only [GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom]
    apply (pointsMulEquiv (R := R) (A := B) n).injective
    rw [HopfAlgebra.mapPoints_apply, HopfAlgebra.mapPoints_apply, ← AlgHom.mapValue_apply,
      ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue,
      pointsMulEquiv_inverseTransposePointsMulEquiv,
      pointsMulEquiv_inverseTransposePointsMulEquiv, pointsMulEquiv_mapValue]
    exact (Matrix.GeneralLinearGroup.map_inverseTranspose (φ.hom : A →+* B) _).symm

/-- The component of `inverseTransposePointsNatIso` at `A` is `inverseTransposePointsMulEquiv`. -/
@[simp]
private theorem inverseTransposePointsNatIso_hom_app_apply (A : CommAlgCat.{u} R)
    (x : (HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n)).obj A) :
    (inverseTransposePointsNatIso R n).hom.app A x = inverseTransposePointsMulEquiv R n A x :=
  rfl

/-- **Inverse transpose on `GLₙ`, in coordinates.** The coordinate Hopf-algebra automorphism of
`GLₙ` over `R` corresponding to the group-scheme automorphism `g ↦ (g⁻¹)ᵀ`. -/
noncomputable def inverseTransposeCoordinateIso :
    coordinateHopfAlgebra R n ≅ coordinateHopfAlgebra R n where
  hom := CommHopfAlgCat.homOfPointsMap (inverseTransposePointsNatIso R n).hom
  inv := CommHopfAlgCat.homOfPointsMap (inverseTransposePointsNatIso R n).inv
  hom_inv_id := by
    rw [← CommHopfAlgCat.homOfPointsMap_comp, Iso.inv_hom_id, CommHopfAlgCat.homOfPointsMap_id]
  inv_hom_id := by
    rw [← CommHopfAlgCat.homOfPointsMap_comp, Iso.hom_inv_id, CommHopfAlgCat.homOfPointsMap_id]

variable {R n}

/-- Precomposition with the inverse-transpose coordinate automorphism, for value algebras in the
universe of the base ring, where it is read off from the natural transformation of points. -/
private theorem pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso_of_univ (A : Type u)
    [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n
        (toConv (f.ofConv.comp ((inverseTransposeCoordinateIso R n).hom.hom :
          coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n))) =
      Matrix.GeneralLinearGroup.inverseTranspose (pointsMulEquiv n f) := by
  rw [← CommHopfAlgCat.Hom.mapPointsFunctor_app_apply (A := CommAlgCat.of R A),
    inverseTransposeCoordinateIso, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap,
    inverseTransposePointsNatIso_hom_app_apply R n (CommAlgCat.of R A) f]
  exact pointsMulEquiv_inverseTransposePointsMulEquiv R n (CommAlgCat.of R A) f

/-- **Precomposing a point of `GLₙ` with the inverse-transpose coordinate automorphism applies
inverse transpose to its matrix**, over a value algebra in any universe. -/
theorem pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso (A : Type v)
    [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n
        (toConv (f.ofConv.comp ((inverseTransposeCoordinateIso R n).hom.hom :
          coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n))) =
      Matrix.GeneralLinearGroup.inverseTranspose (pointsMulEquiv n f) := by
  -- Every point is the image of the universal point `AlgHom.id` under its own value map, so the
  -- formula follows from its case over the coordinate algebra, by naturality in the values.
  have huniv := pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso_of_univ
    (coordinateHopfAlgebra R n) (toConv (AlgHom.id R (coordinateHopfAlgebra R n)))
  rw [ofConv_toConv, AlgHom.id_comp] at huniv
  have hf : pointsMulEquiv n f =
      Matrix.GeneralLinearGroup.map (f.ofConv : coordinateHopfAlgebra R n →+* A)
        (pointToGeneralLinear n (toConv (AlgHom.id R (coordinateHopfAlgebra R n)))) := by
    rw [pointsMulEquiv_apply, ← pointToGeneralLinear_toConv_comp, ofConv_toConv, AlgHom.comp_id,
      toConv_ofConv]
  rw [pointsMulEquiv_apply, pointToGeneralLinear_toConv_comp, ← pointsMulEquiv_apply, huniv, hf,
    pointsMulEquiv_apply]
  exact Matrix.GeneralLinearGroup.map_inverseTranspose (n := Fin n)
    (f.ofConv : coordinateHopfAlgebra R n →+* A) _

/-- Inverse transpose on the functor of points of `GLₙ` is an involution. -/
private theorem inverseTransposePointsNatIso_hom_comp_self :
    (inverseTransposePointsNatIso R n).hom ≫ (inverseTransposePointsNatIso R n).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext A
  apply GrpCat.ext
  intro x
  rw [NatTrans.comp_app, GrpCat.comp_apply, NatTrans.id_app, GrpCat.id_apply,
    inverseTransposePointsNatIso_hom_app_apply, inverseTransposePointsNatIso_hom_app_apply]
  exact inverseTransposePointsMulEquiv_apply_apply R n A x

/-- **Inverse transpose is an involution of `GLₙ`**, in coordinates. -/
@[reassoc (attr := simp)]
theorem inverseTransposeCoordinateIso_hom_comp_self :
    (inverseTransposeCoordinateIso R n).hom ≫ (inverseTransposeCoordinateIso R n).hom =
      𝟙 (coordinateHopfAlgebra R n) := by
  rw [inverseTransposeCoordinateIso, ← CommHopfAlgCat.homOfPointsMap_comp,
    inverseTransposePointsNatIso_hom_comp_self, CommHopfAlgCat.homOfPointsMap_id]

/-- The inverse of the inverse-transpose coordinate automorphism is itself. -/
@[simp]
theorem inverseTransposeCoordinateIso_symm :
    (inverseTransposeCoordinateIso R n).symm = inverseTransposeCoordinateIso R n :=
  Iso.ext <| by
    rw [Iso.symm_hom, ← cancel_epi (inverseTransposeCoordinateIso R n).hom, Iso.hom_inv_id,
      inverseTransposeCoordinateIso_hom_comp_self]

/-- **The fixed points of inverse transpose are the orthogonal matrices.** A point of `GLₙ` is
fixed by the inverse-transpose coordinate automorphism exactly when its matrix is orthogonal; over
`ℝ` these are the real points of `O(n)`. -/
theorem toConv_comp_inverseTransposeCoordinateIso_eq_self_iff (A : Type v)
    [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    toConv (f.ofConv.comp ((inverseTransposeCoordinateIso R n).hom.hom :
        coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n)) = f ↔
      pointsMulEquiv n f ∈ GLOrthogonal (Fin n) A := by
  rw [GLOrthogonal.mem_iff_inverseTranspose_eq,
    ← pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso, (pointsMulEquiv n).injective.eq_iff]

end TauCeti.GeneralLinear
