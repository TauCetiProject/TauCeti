/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.RootSubgroup

/-!
# The type-A graph involution preserves the standard Borel

Signed reverse inverse transpose preserves the upper-triangular subgroup scheme of
`SL_{r+1}` over every commutative base ring. This is the standard Borel in the special-linear
pinning. The assertion is scheme-theoretic: the coordinate automorphism preserves its Hopf
ideal and induces an involution of its coordinate algebra and group scheme. No reducedness
hypothesis on the base or value algebra is needed.

The restricted involution agrees with the ambient graph automorphism under the closed
inclusion and reverses the numbered positive simple-root subgroups without changing their
parameters. These equations express the Borel compatibility required of the pinned diagram
automorphism; they do not assert a general isomorphism theorem for pinned groups.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 12.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.

The matrix normalization is `TauCeti.typeAGraphAutomorphism`. The construction uses
`TauCeti.CommHopfAlgCat.quotientIsoOfComapEq` to restrict the represented special-linear
graph involution to the upper-triangular quotient.
-/

public section

open CategoryTheory WithConv AlgebraicGeometry

namespace TauCeti.SpecialLinear.UpperTriangular

universe u v

variable (R : Type u) [CommRing R] (r : ℕ)

/-- Precomposition with the graph coordinate automorphism preserves the upper-triangular
point subgroup over every commutative value algebra. -/
@[simp↓]
theorem mem_definingPointsSubgroup_comp_typeAGraphCoordinateIso_iff
    (A : Type v) [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points (R := R) (H := SpecialLinear.coordinateHopfAlgebra R (r + 1))
      (CommAlgCat.of R A)) :
    toConv (f.ofConv.comp (SpecialLinear.typeAGraphCoordinateIso R r).hom.hom.toAlgHom) ∈
        CommHopfAlgCat.quotientPointsSubgroup
          (SpecialLinear.coordinateHopfAlgebra R (r + 1)) (definingHopfIdeal R (r + 1))
          (CommAlgCat.of R A) ↔
      f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (SpecialLinear.coordinateHopfAlgebra R (r + 1)) (definingHopfIdeal R (r + 1))
        (CommAlgCat.of R A) := by
  rw [mem_definingPointsSubgroup_iff, mem_definingPointsSubgroup_iff,
    SpecialLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso,
    Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism,
    TauCeti.typeAGraphAutomorphism_mem_upperTriangularGroup_iff]

private theorem typeAGraphCoordinateIso_hom_mem (x : SpecialLinear.coordinateHopfAlgebra R (r + 1))
    (hx : x ∈ definingHopfIdeal R (r + 1)) :
    (SpecialLinear.typeAGraphCoordinateIso R r).hom.hom x ∈ definingHopfIdeal R (r + 1) := by
  -- Test on the universal point of the quotient, not just on field-valued points.
  let A := coordinateHopfAlgebra R (r + 1)
  let q : HopfAlgebra.points (R := R) (H := SpecialLinear.coordinateHopfAlgebra R (r + 1))
      (CommAlgCat.of R A) := toConv (coordinateMap R (r + 1)).hom.toAlgHom
  have hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup
      (SpecialLinear.coordinateHopfAlgebra R (r + 1)) (definingHopfIdeal R (r + 1))
      (CommAlgCat.of R A) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ y).mpr hy
  have hgraph := (mem_definingPointsSubgroup_comp_typeAGraphCoordinateIso_iff R r A q).mpr hq
  have hz := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hgraph x hx
  exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mp hz

/-- The graph automorphism pulls the standard upper-triangular Hopf ideal back to itself.
This holds over the base ring, including in positive characteristic and over nilpotents. -/
theorem comap_definingHopfIdeal_typeAGraphCoordinateIso :
    (definingHopfIdeal R (r + 1)).comapOfSurjective
        (SpecialLinear.typeAGraphCoordinateIso R r).hom.hom
        (ConcreteCategory.bijective_of_isIso (SpecialLinear.typeAGraphCoordinateIso R r).hom).2 =
      definingHopfIdeal R (r + 1) := by
  have hhom : (definingHopfIdeal R (r + 1)).comapOfSurjective
      (SpecialLinear.typeAGraphCoordinateIso R r).hom.hom
      (ConcreteCategory.bijective_of_isIso (SpecialLinear.typeAGraphCoordinateIso R r).hom).2 ≤
        definingHopfIdeal R (r + 1) := by
    intro x hx
    have hback := typeAGraphCoordinateIso_hom_mem R r _
      (HopfIdeal.mem_comapOfSurjective.mp hx)
    have hcancel := CommHopfAlgCat.inv_hom_apply (SpecialLinear.typeAGraphCoordinateIso R r) x
    simp only [SpecialLinear.typeAGraphCoordinateIso_inv] at hcancel
    exact hcancel ▸ hback
  exact HopfIdeal.comapOfSurjective_eq_of_hom_le_of_inv_le _ _ hhom
    (by simpa only [SpecialLinear.typeAGraphCoordinateIso_inv] using hhom)

/-- The coordinate graph involution restricted to the upper-triangular subgroup of `SL_{r+1}`. -/
noncomputable def typeAGraphCoordinateIso :
    coordinateHopfAlgebra R (r + 1) ≅ coordinateHopfAlgebra R (r + 1) :=
  CommHopfAlgCat.quotientIsoOfComapEq (SpecialLinear.typeAGraphCoordinateIso R r)
    (definingHopfIdeal R (r + 1)) (comap_definingHopfIdeal_typeAGraphCoordinateIso R r)

/-- Restriction of coordinates intertwines the ambient and upper-triangular graph maps. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_typeAGraphCoordinateIso_hom :
    coordinateMap R (r + 1) ≫ (typeAGraphCoordinateIso R r).hom =
      (SpecialLinear.typeAGraphCoordinateIso R r).hom ≫ coordinateMap R (r + 1) :=
  CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom _ _ _

/-- The restricted coordinate graph map squares to the identity. -/
@[simp]
theorem typeAGraphCoordinateIso_hom_comp_self :
    (typeAGraphCoordinateIso R r).hom ≫ (typeAGraphCoordinateIso R r).hom =
      𝟙 (coordinateHopfAlgebra R (r + 1)) := by
  let _ : Epi (coordinateMap R (r + 1)) := CommHopfAlgCat.mkQuotient_epi
  rw [← cancel_epi (coordinateMap R (r + 1)),
    coordinateMap_comp_typeAGraphCoordinateIso_hom_assoc,
    coordinateMap_comp_typeAGraphCoordinateIso_hom, ← Category.assoc,
    SpecialLinear.typeAGraphCoordinateIso_hom_comp_self]
  simp

/-- The inverse restricted graph map is its forward map. -/
@[simp]
theorem typeAGraphCoordinateIso_inv :
    (typeAGraphCoordinateIso R r).inv = (typeAGraphCoordinateIso R r).hom := by
  rw [← cancel_epi (typeAGraphCoordinateIso R r).hom]
  simp

/-- On all algebra-valued points, the restricted graph involution is signed reverse
inverse transpose on the underlying determinant-one matrix. -/
@[simp↓]
theorem pointsMulEquiv_comp_typeAGraphCoordinateIso
    (A : Type v) [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R (r + 1))
      (CommAlgCat.of R A)) :
    (pointsMulEquiv R (r + 1) (A := A)
        (toConv (f.ofConv.comp (typeAGraphCoordinateIso R r).hom.hom.toAlgHom)) :
          Matrix.SpecialLinearGroup (Fin (r + 1)) A) =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (pointsMulEquiv R (r + 1) (A := A) f) := by
  rw [← pointsMulEquiv_coe, CommHopfAlgCat.quotientPointsHom_apply]
  have hcomp := congrArg (fun g => g.hom.toAlgHom)
    (coordinateMap_comp_typeAGraphCoordinateIso_hom R r)
  rw [CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    BialgHom.comp_toAlgHom] at hcomp
  rw [ofConv_toConv, AlgHom.comp_assoc, hcomp, ← AlgHom.comp_assoc,
    SpecialLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso,
    ← CommHopfAlgCat.quotientPointsHom_apply, pointsMulEquiv_coe]

/-- The graph involution of the upper-triangular group scheme, obtained by relative spectrum
of its restricted coordinate involution. -/
noncomputable def typeAGraphIso :
    CommHopfAlgCat.quotientSpec (SpecialLinear.coordinateHopfAlgebra R (r + 1))
        (definingHopfIdeal R (r + 1)) ≅
      CommHopfAlgCat.quotientSpec (SpecialLinear.coordinateHopfAlgebra R (r + 1))
        (definingHopfIdeal R (r + 1)) :=
  (hopfSpec (CommRingCat.of R)).mapIso (typeAGraphCoordinateIso R r).op

/-- The restricted group-scheme involution commutes with the standard closed inclusion
into the special linear group scheme. -/
@[reassoc (attr := simp)]
theorem typeAGraphIso_hom_comp_quotientSpecι :
    (typeAGraphIso R r).hom ≫
        CommHopfAlgCat.quotientSpecι _ (definingHopfIdeal R (r + 1)) ≫
          eqToHom (SpecialLinear.groupScheme_def R (r + 1)).symm =
      CommHopfAlgCat.quotientSpecι _ (definingHopfIdeal R (r + 1)) ≫
        eqToHom (SpecialLinear.groupScheme_def R (r + 1)).symm ≫
          (SpecialLinear.typeAGraphIso R r).hom := by
  simp only [typeAGraphIso, Functor.mapIso_hom, Iso.op_hom,
    SpecialLinear.typeAGraphIso_hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def, ← Functor.map_comp_assoc,
    ← op_comp, coordinateMap_comp_typeAGraphCoordinateIso_hom,
    op_comp, Functor.map_comp]
  simp

/-- The group-scheme graph map restricted to the standard Borel is involutive. -/
@[simp]
theorem typeAGraphIso_hom_comp_self :
    (typeAGraphIso R r).hom ≫ (typeAGraphIso R r).hom =
      𝟙 (CommHopfAlgCat.quotientSpec (SpecialLinear.coordinateHopfAlgebra R (r + 1))
        (definingHopfIdeal R (r + 1))) := by
  simp only [typeAGraphIso, Functor.mapIso_hom, Iso.op_hom,
    ← Functor.map_comp, ← op_comp, typeAGraphCoordinateIso_hom_comp_self,
    op_id]
  exact (hopfSpec (CommRingCat.of R)).map_id _

/-- The inverse graph map of the standard Borel is its forward map. -/
@[simp]
theorem typeAGraphIso_inv :
    (typeAGraphIso R r).inv = (typeAGraphIso R r).hom := by
  rw [← cancel_epi (typeAGraphIso R r).hom]
  simp

/-- The restricted group-scheme involution reverses the positive simple-root subgroups
with parameter unchanged. -/
@[reassoc (attr := simp↓)]
theorem rootSubgroup_comp_typeAGraphIso_hom (i : Fin r) :
    rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i)) ≫ (typeAGraphIso R r).hom =
      rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i.rev)) := by
  apply (cancel_mono (CommHopfAlgCat.quotientSpecι _ (definingHopfIdeal R (r + 1)) ≫
    eqToHom (SpecialLinear.groupScheme_def R (r + 1)).symm)).1
  simp only [Category.assoc, typeAGraphIso_hom_comp_quotientSpecι,
    rootSubgroup_comp_quotientSpecι_assoc, rootSubgroup_comp_quotientSpecι,
    SpecialLinear.rootSubgroup_comp_typeAGraphIso_hom]

end TauCeti.SpecialLinear.UpperTriangular
