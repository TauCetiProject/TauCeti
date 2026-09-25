/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Algebra.Hom
public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier

/-!
# The points of the type-F4 short-root carrier, functorially

`TauCeti.F4ShortRoot.groupScheme` is the explicit short-root type-`F₄` carrier over `ℤ`, built
from the `26`-dimensional short-root representation, and `TauCeti.F4ShortRoot.points A` realizes its
`A`-valued points as a subgroup of `GL₂₆(A)`. This file supplies the homomorphism induced by an
arbitrary homomorphism of value rings and assembles these point groups into a functor on
commutative `ℤ`-algebras.

The induced map is entrywise and preserves the two pinned families:

```text
f (x_k(u)) = x_k(f(u)),        f (t(s)) = t(f ∘ s).
```

The quotient of the ambient general-linear coordinate Hopf algebra by the short-root carrier's
defining ideal represents this functor. Nothing here asserts reductivity, maximality of the
weight torus, or an identification of the carrier's root datum.

## Main declarations

* `TauCeti.F4ShortRoot.pointsPresentation`: the generic integral presentation of the named points.
* `TauCeti.F4ShortRoot.pointsMap`: the map on carrier points induced by a ring homomorphism.
* `TauCeti.F4ShortRoot.pointsFunctor`: the group-valued functor of points.
* `TauCeti.F4ShortRoot.pointsMulEquiv`: the pointwise representing isomorphism.
* `TauCeti.F4ShortRoot.pointsFunctorNatIso`: the natural representing isomorphism.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

-/

public section

open CategoryTheory

namespace TauCeti.F4ShortRoot

universe v v'

noncomputable section

/-- The named short-root carrier points, packaged as an integral Hopf-ideal presentation. -/
def pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 26 definingIdeal A :=
  ⟨points A, points_def A⟩

section Map

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The map on the points of the short-root type-`F₄` carrier induced by a homomorphism of value
rings. It is the entrywise map on `GL₂₆`, restricted to the subgroup cut out by the carrier's
defining ideal. -/
def pointsMap (f : A →+* B) : points A →* points B :=
  (pointsPresentation A).map (pointsPresentation B) f

/-- The induced map on short-root type-`F₄` carrier points is the entrywise map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points A) :
    (pointsMap f g : Matrix.GeneralLinearGroup (Fin 26) B) =
      Matrix.GeneralLinearGroup.map f g := by
  exact (pointsPresentation A).coe_map (pointsPresentation B) f g

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points A) (i j : Fin 26) :
    ((pointsMap f g : Matrix.GeneralLinearGroup (Fin 26) B) :
        Matrix (Fin 26) (Fin 26) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on short-root type-`F₄` carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap (RingHom.id A) = MonoidHom.id _ := by
  exact (pointsPresentation A).map_id

/-- The induced maps on short-root type-`F₄` carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap (g.comp f) = (pointsMap g).comp (pointsMap f) := by
  exact (pointsPresentation A).map_comp (pointsPresentation B) (pointsPresentation C) f g

/-- An injective homomorphism of value rings induces an injective map on the points of the
short-root type-`F₄` carrier. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap f) :=
  (pointsPresentation A).map_injective (pointsPresentation B) hf

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B) (k : Fin 4 ⊕ Fin 4)
    (u : Multiplicative A) :
    pointsMap f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.F₄.transpose))
      (h := TauCeti.serreH ℚ (CartanMatrix.F₄.transpose)) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := latticeBasis)
      (wt := TauCeti.DynkinType.f4ShortRootWeight) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin 4 → Aˣ) :
    pointsMap f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.F₄.transpose))
      (h := TauCeti.serreH ℚ (CartanMatrix.F₄.transpose)) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := latticeBasis)
      (wt := TauCeti.DynkinType.f4ShortRootWeight) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using h

end Map

/-! ## The functor of points -/

/-- The group-valued functor of points of the short-root type-`F₄` carrier. -/
def pointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} :=
  GeneralLinear.IntegralPointsPresentation.functor pointsPresentation

/-- The object part of the short-root carrier's points functor is its named point group. -/
@[simp]
theorem pointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    pointsFunctor.obj A = GrpCat.of (points A) :=
  GeneralLinear.IntegralPointsPresentation.functor_obj pointsPresentation A

/-- The morphism part of the short-root carrier's points functor is the induced entrywise map. -/
@[simp]
theorem pointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    pointsFunctor.map f =
      eqToHom (pointsFunctor_obj A) ≫ GrpCat.ofHom (pointsMap f.hom) ≫
        eqToHom (pointsFunctor_obj B).symm :=
  GeneralLinear.IntegralPointsPresentation.functor_map pointsPresentation f

/-- The points of the quotient coordinate Hopf algebra are the named short-root carrier points. -/
def pointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) A ≃*
      points A :=
  (pointsPresentation A).mulEquiv

/-- A quotient point, read through `pointsMulEquiv`, is its ambient point viewed as an invertible
matrix. -/
@[simp]
theorem coe_pointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) A) :
    (pointsMulEquiv A q : Matrix.GeneralLinearGroup (Fin 26) A) =
      GeneralLinear.pointsMulEquiv 26
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal A q) := by
  exact (pointsPresentation A).coe_mulEquiv_apply q

/-- Including the ambient Hopf-algebra point underlying the inverse of `pointsMulEquiv` recovers
the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (A : CommAlgCat.{v} ℤ) (g : points A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal A
        ((pointsMulEquiv A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) 26).symm
        (g : Matrix.GeneralLinearGroup (Fin 26) A) := by
  exact (pointsPresentation A).quotientPointsHom_mulEquiv_symm g

/-- The pointwise identification with quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem pointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) A) :
    pointsMulEquiv B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) f q) =
      pointsMap f.hom (pointsMulEquiv A q) := by
  exact (pointsPresentation A).mulEquiv_mapPoints (pointsPresentation B) f q

/-- The quotient coordinate Hopf algebra represents the points functor of the type-`F₄`
short-root carrier. -/
def pointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) ≅
      pointsFunctor :=
  GeneralLinear.IntegralPointsPresentation.natIso pointsPresentation

/-- The forward component of the representing natural isomorphism is the pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 26) definingIdeal) A) :
    eqToHom (pointsFunctor_obj A) (pointsFunctorNatIso.hom.app A q) = pointsMulEquiv A q :=
  GeneralLinear.IntegralPointsPresentation.natIso_hom_app_apply pointsPresentation A q

/-- The inverse component of the representing natural isomorphism is the inverse pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : points A) :
    pointsFunctorNatIso.inv.app A (eqToHom (pointsFunctor_obj A).symm g) =
      (pointsMulEquiv A).symm g :=
  GeneralLinear.IntegralPointsPresentation.natIso_inv_app_apply pointsPresentation A g

end

end TauCeti.F4ShortRoot
