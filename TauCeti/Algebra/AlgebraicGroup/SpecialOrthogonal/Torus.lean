/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo

/-!
# The two-dimensional special orthogonal torus

Suppose a commutative ring `R` contains a square root `i` of `-1` and an element `half` with
`2 * half = 1`. The standard special orthogonal group `SO₂` is then the rank-one split torus.
On points, the identification sends a torus coordinate `u` to

```text
half * (u + u⁻¹)       -i * half * (u - u⁻¹)
i * half * (u - u⁻¹)   half * (u + u⁻¹).
```

The pointwise equivalence is natural in the value algebra. Full faithfulness of the functor of
points therefore recovers an isomorphism between the coordinate Hopf algebra of the rank-one
split torus and `O(SO₂)`. Over a field of characteristic different from two, an algebraic closure
contains the required square root, so `SO₂` is a (possibly non-split) one-dimensional torus over
the original field. In particular it is reductive.

## Main declarations

* `TauCeti.SpecialOrthogonal.splitTorusPointsMulEquiv`: the natural pointwise identification of
  the rank-one split torus with `SO₂`.
* `TauCeti.SpecialOrthogonal.splitTorusCoordinateIso`: the corresponding coordinate Hopf-algebra
  isomorphism.
* `TauCeti.SpecialOrthogonal.torusCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two`:
  `SO₂` is a torus over every field of characteristic different from two.
* `TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two`:
  `SO₂` is reductive under the same hypothesis.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3, 12 and 18.c.
* T. A. Springer, *Linear Algebraic Groups*, §7.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialOrthogonal

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-- Evaluation at the unique coordinate identifies a one-entry family of units with the unit
group. -/
private def rankOneCoordinatesMulEquiv (A : Type v) [CommRing A] :
    (ULift.{u} (Fin 1) → Aˣ) ≃* Aˣ :=
  MulEquiv.piUnique (fun _ : ULift.{u} (Fin 1) ↦ Aˣ)

/-- A one-entry family of units determines a two-dimensional special orthogonal matrix. -/
private def rankOneCoordinatesSpecialOrthogonalMulEquiv
    (A : Type v) [CommRing A] (i half : A) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) :
    (ULift.{u} (Fin 1) → Aˣ) ≃* Matrix.specialOrthogonalGroup (Fin 2) A :=
  (rankOneCoordinatesMulEquiv A).trans
    (Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits i half hi hhalf).symm

/-- The rank-one-coordinate matrix equivalence commutes with a ring morphism which preserves
the chosen square root and half. -/
private theorem map_rankOneCoordinatesSpecialOrthogonalMulEquiv
    {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (i half : A) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1)
    (c : ULift.{u} (Fin 1) → Aˣ) :
    Matrix.SpecialOrthogonalGroup.map f
        (rankOneCoordinatesSpecialOrthogonalMulEquiv A i half hi hhalf c) =
      rankOneCoordinatesSpecialOrthogonalMulEquiv B (f i) (f half)
        (by simpa only [map_pow, map_neg, map_one] using congrArg f hi)
        (by simpa only [map_ofNat, map_mul, map_one] using congrArg f hhalf)
        (fun j ↦ Units.map f (c j)) := by
  simp only [rankOneCoordinatesSpecialOrthogonalMulEquiv, MulEquiv.trans_apply,
    rankOneCoordinatesMulEquiv]
  rw [Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits_symm_apply,
    Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits_symm_apply,
    Matrix.SpecialOrthogonalGroup.map_finTwoOfUnit]
  congr 1

variable (i half : R) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1)

/-- **The points of the rank-one split torus are naturally the points of `SO₂`** when the base
contains a square root of `-1` and a half. -/
noncomputable def splitTorusPointsMulEquiv (A : Type v) [CommRing A] [Algebra R A] :
    WithConv ((DiagonalizableGroup.coordinateRing R
      (SplitTorus.characterGroup (ULift.{u} (Fin 1)))) →ₐ[R] A) ≃*
      WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A) :=
  SplitTorus.pointsMulEquiv.trans
    ((rankOneCoordinatesSpecialOrthogonalMulEquiv A
      (algebraMap R A i) (algebraMap R A half)
      (by simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap R A) hi)
      (by simpa only [map_ofNat, map_mul, map_one] using
        congrArg (algebraMap R A) hhalf)).trans
      (pointsMulEquiv R 2 (A := A)).symm)

/-- The split-torus point equivalence sends a point to the special orthogonal matrix obtained
from its unique unit coordinate. -/
private theorem pointsMulEquiv_splitTorusPointsMulEquiv
    (A : Type v) [CommRing A] [Algebra R A]
    (t : WithConv ((DiagonalizableGroup.coordinateRing R
      (SplitTorus.characterGroup (ULift.{u} (Fin 1)))) →ₐ[R] A)) :
    pointsMulEquiv R 2 (A := A) (splitTorusPointsMulEquiv R i half hi hhalf A t) =
      rankOneCoordinatesSpecialOrthogonalMulEquiv A
        (algebraMap R A i) (algebraMap R A half)
        (by simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap R A) hi)
        (by simpa only [map_ofNat, map_mul, map_one] using
          congrArg (algebraMap R A) hhalf)
        (SplitTorus.pointsMulEquiv t) := by
  rw [splitTorusPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

/-- The split-torus point equivalence sends a point to the point represented by the
two-dimensional special orthogonal matrix attached to its unique unit coordinate. -/
@[simp]
theorem splitTorusPointsMulEquiv_apply
    (A : Type v) [CommRing A] [Algebra R A]
    (t : WithConv ((DiagonalizableGroup.coordinateRing R
      (SplitTorus.characterGroup (ULift.{u} (Fin 1)))) →ₐ[R] A)) :
    splitTorusPointsMulEquiv R i half hi hhalf A t =
      (pointsMulEquiv R 2 (A := A)).symm
        (Matrix.SpecialOrthogonalGroup.finTwoOfUnit
          (algebraMap R A i) (algebraMap R A half)
          (by simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap R A) hi)
          (by simpa only [map_ofNat, map_mul, map_one] using
            congrArg (algebraMap R A) hhalf)
          (SplitTorus.pointsMulEquiv t default)) := by
  apply (pointsMulEquiv R 2 (A := A)).injective
  rw [MulEquiv.apply_symm_apply, pointsMulEquiv_splitTorusPointsMulEquiv]
  rw [rankOneCoordinatesSpecialOrthogonalMulEquiv, MulEquiv.trans_apply,
    Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits_symm_apply]
  rfl

/-- The inverse split-torus point equivalence reads off the unit of a two-dimensional special
orthogonal matrix and makes it the unique split-torus coordinate. -/
@[simp]
theorem splitTorusPointsMulEquiv_symm_apply
    (A : Type v) [CommRing A] [Algebra R A]
    (s : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (splitTorusPointsMulEquiv R i half hi hhalf A).symm s =
      (SplitTorus.pointsMulEquiv (R := R) (A := A)).symm
        (fun _ ↦ Matrix.SpecialOrthogonalGroup.finTwoToUnit
          (algebraMap R A i)
          (by simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap R A) hi)
          (pointsMulEquiv R 2 (A := A) s)) := by
  rw [splitTorusPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    rankOneCoordinatesSpecialOrthogonalMulEquiv, MulEquiv.symm_trans_apply]
  simp only [MulEquiv.symm_symm]
  rw [
    Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits_apply]
  rfl

/-- The rank-one split-torus point equivalence is natural in the commutative value algebra. -/
theorem splitTorusPointsMulEquiv_mapValue
    {A B : Type v} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B)
    (t : WithConv ((DiagonalizableGroup.coordinateRing R
      (SplitTorus.characterGroup (ULift.{u} (Fin 1)))) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R 2) f
        (splitTorusPointsMulEquiv R i half hi hhalf A t) =
      splitTorusPointsMulEquiv R i half hi hhalf B
        (AlgHom.mapValue (H := (DiagonalizableGroup.coordinateRing R
          (SplitTorus.characterGroup (ULift.{u} (Fin 1)))).obj) f t) := by
  apply (pointsMulEquiv R 2 (A := B)).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_splitTorusPointsMulEquiv,
    pointsMulEquiv_splitTorusPointsMulEquiv]
  rw [map_rankOneCoordinatesSpecialOrthogonalMulEquiv]
  simp only [← f.commutes i, ← f.commutes half]
  congr 1
  funext j
  exact (SplitTorus.pointsMulEquiv_mapValue f t j).symm

/-- The natural isomorphism between the group-valued functors of points of the rank-one split
torus and `SO₂`. -/
noncomputable def splitTorusPointsNatIso :
    HopfAlgebra.pointsFunctor.{u} (R := R) (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 1)))).obj) ≅
      HopfAlgebra.pointsFunctor.{u} (R := R) (H := coordinateHopfAlgebra R 2) :=
  NatIso.ofComponents
    (fun A ↦ (splitTorusPointsMulEquiv R i half hi hhalf A).toGrpIso)
    (fun {A B} f ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro t
      exact (splitTorusPointsMulEquiv_mapValue R i half hi hhalf f.hom t).symm)

/-- The forward component of the natural split-torus identification is the pointwise
equivalence `splitTorusPointsMulEquiv`. -/
@[simp]
theorem splitTorusPointsNatIso_hom_app_apply
    (A : CommAlgCat.{u} R)
    (t : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 1)))).obj) A) :
    (splitTorusPointsNatIso R i half hi hhalf).hom.app A t =
      splitTorusPointsMulEquiv R i half hi hhalf A t :=
  by unfold splitTorusPointsNatIso; rfl

/-- The inverse component of the natural split-torus identification is the inverse pointwise
equivalence `splitTorusPointsMulEquiv`. -/
@[simp]
theorem splitTorusPointsNatIso_inv_app_apply
    (A : CommAlgCat.{u} R)
    (s : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    (splitTorusPointsNatIso R i half hi hhalf).inv.app A s =
      (splitTorusPointsMulEquiv R i half hi hhalf A).symm s :=
  by unfold splitTorusPointsNatIso; rfl

/-- **The coordinate Hopf algebra of `SO₂` is the coordinate Hopf algebra of the rank-one split
torus** when the base contains a square root of `-1` and a half. -/
noncomputable def splitTorusCoordinateIso :
    (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 1)))).obj ≅
      coordinateHopfAlgebra R 2 :=
  ((CommHopfAlgCat.pointsFunctor (R := R)).preimageIso
    (splitTorusPointsNatIso R i half hi hhalf).symm).unop

/-- On every value algebra, the point map induced by the forward coordinate isomorphism is the
inverse pointwise split-torus equivalence. -/
@[simp]
theorem mapPointsFunctor_splitTorusCoordinateIso_hom_app_apply
    (A : CommAlgCat.{u} R)
    (s : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    (CommHopfAlgCat.mapPointsFunctor (splitTorusCoordinateIso R i half hi hhalf).hom).app A s =
      (splitTorusPointsMulEquiv R i half hi hhalf A).symm s := by
  have hmap :
      CommHopfAlgCat.mapPointsFunctor (splitTorusCoordinateIso R i half hi hhalf).hom =
        (splitTorusPointsNatIso R i half hi hhalf).inv := by
    -- `pointsFunctor_map` does not cancel `op`/`unop` at rewrite transparency.
    -- Reduce them here to expose the categorical map needed by `Functor.map_preimage`.
    change (CommHopfAlgCat.pointsFunctor (R := R)).map
        (splitTorusCoordinateIso R i half hi hhalf).hom.op = _
    rw [splitTorusCoordinateIso]
    -- `preimageIso_hom` cannot match at rewrite transparency: its object types require
    -- reducing `pointsFunctor.obj`. This `change` performs that reduction, cancels
    -- `op`/`unop`, and projects the preimage isomorphism's forward component.
    change (CommHopfAlgCat.pointsFunctor (R := R)).map
        ((CommHopfAlgCat.pointsFunctor (R := R)).preimage
          (splitTorusPointsNatIso R i half hi hhalf).symm.hom) = _
    exact Functor.map_preimage (CommHopfAlgCat.pointsFunctor (R := R)) _
  rw [hmap]
  exact splitTorusPointsNatIso_inv_app_apply R i half hi hhalf A s

/-- On every value algebra, the point map induced by the inverse coordinate isomorphism is the
forward pointwise split-torus equivalence. -/
@[simp]
theorem mapPointsFunctor_splitTorusCoordinateIso_inv_app_apply
    (A : CommAlgCat.{u} R)
    (t : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 1)))).obj) A) :
    (CommHopfAlgCat.mapPointsFunctor (splitTorusCoordinateIso R i half hi hhalf).inv).app A t =
      splitTorusPointsMulEquiv R i half hi hhalf A t := by
  have hmap :
      CommHopfAlgCat.mapPointsFunctor (splitTorusCoordinateIso R i half hi hhalf).inv =
        (splitTorusPointsNatIso R i half hi hhalf).hom := by
    -- `pointsFunctor_map` does not cancel `op`/`unop` at rewrite transparency.
    -- Reduce them here to expose the categorical map needed by `Functor.map_preimage`.
    change (CommHopfAlgCat.pointsFunctor (R := R)).map
        (splitTorusCoordinateIso R i half hi hhalf).inv.op = _
    rw [splitTorusCoordinateIso]
    -- `preimageIso_inv` cannot match at rewrite transparency: its object types require
    -- reducing `pointsFunctor.obj`. This `change` performs that reduction, cancels
    -- `op`/`unop`, and projects the preimage isomorphism's inverse component.
    change (CommHopfAlgCat.pointsFunctor (R := R)).map
        ((CommHopfAlgCat.pointsFunctor (R := R)).preimage
          (splitTorusPointsNatIso R i half hi hhalf).symm.inv) = _
    exact Functor.map_preimage (CommHopfAlgCat.pointsFunctor (R := R)) _
  rw [hmap]
  exact splitTorusPointsNatIso_hom_app_apply R i half hi hhalf A t

/-- The finite-type coordinate Hopf algebra of `SO₂` is isomorphic to the standard rank-one
split-torus coordinate Hopf algebra under the same splitting hypotheses. -/
noncomputable def finiteTypeSplitTorusCoordinateIso :
    DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 1))) ≅
      finiteTypeCoordinateHopfAlgebra R 2 :=
  ObjectProperty.isoMk _ <| (splitTorusCoordinateIso R i half hi hhalf) ≪≫
    eqToIso (finiteTypeCoordinateHopfAlgebra_obj R 2).symm

/-- When the base contains a square root of `-1` and a half, `SO₂` is a split torus of rank
one. -/
theorem splitTorusCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two
    (i half : R) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) :
    splitTorusCommHopfAlgProperty R (finiteTypeCoordinateHopfAlgebra R 2) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨1, ⟨finiteTypeSplitTorusCoordinateIso R i half hi hhalf⟩⟩

section Field

variable (k : Type u) [Field k] [NeZero (2 : k)]

/-- **The standard two-dimensional special orthogonal group is a torus** over every field of
characteristic different from two. It need not be split over the ground field. -/
theorem torusCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two :
    torusCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k 2) := by
  let K := AlgebraicClosure k
  have h2 : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap k K)).2 (NeZero.ne (2 : k))
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by norm_num)
  let half : K := (2 : K)⁻¹
  have hhalf : 2 * half = 1 := mul_inv_cancel₀ h2
  rw [torusCommHopfAlgProperty_iff]
  exact ⟨1, ⟨
    finiteTypeSplitTorusCoordinateIso K i half hi hhalf ≪≫
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K 2).symm⟩⟩

/-- **The standard two-dimensional special orthogonal group is reductive** over every field of
characteristic different from two. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k 2) :=
  (torusCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two k).reductive

end Field

end

end TauCeti.SpecialOrthogonal
