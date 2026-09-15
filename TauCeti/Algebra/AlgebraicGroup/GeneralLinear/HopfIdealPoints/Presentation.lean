/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
import TauCeti.Algebra.Algebra.Hom

/-!
# Presented matrix points over the integers

A subgroup of `GLₙ(A)` presented by a fixed integral Hopf ideal inherits entrywise maps of
value rings and a representing equivalence with points of the quotient coordinate algebra.
`IntegralPointsPresentation` records the subgroup and its presentation. Its API supplies these
constructions uniformly, including their functoriality and naturality.

A family of presentations over commutative rings determines a group-valued functor on
commutative `ℤ`-algebras. The quotient coordinate Hopf algebra represents this functor.
Presentations over different universes can be used together in the induced maps of points.

The constructions transport the API of
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor` along the presentation
equalities. The specialization to `ℤ` allows arbitrary ring homomorphisms as value-ring maps.

## Formal provenance

This API is extracted from the functorial-points interfaces of the seven integral carriers:

* `TauCeti.SlStd` ([#5212](https://github.com/TauCetiProject/TauCeti/pull/5212)) and
  `TauCeti.SpStd` ([#5172](https://github.com/TauCetiProject/TauCeti/pull/5172));
* `TauCeti.TypeBSpinCarrier`
  ([#5552](https://github.com/TauCetiProject/TauCeti/pull/5552)) and
  `TauCeti.TypeDSpinCarrier`
  ([#5353](https://github.com/TauCetiProject/TauCeti/pull/5353));
* `TauCeti.E6Minuscule` ([#5265](https://github.com/TauCetiProject/TauCeti/pull/5265)),
  `TauCeti.E6DoubledMinuscule`
  ([#5404](https://github.com/TauCetiProject/TauCeti/pull/5404)), and
  `TauCeti.E7Minuscule` ([#5471](https://github.com/TauCetiProject/TauCeti/pull/5471)).

Those interfaces supplied the declaration order and proof templates consolidated here. The
doubled E₆ and E₇ interfaces followed the E₆ minuscule interface; the E₆ minuscule and type-D
interfaces followed the type-A and type-C interfaces. The type-B interface followed the type-D
spin interface. The earlier type-A and type-C interfaces also drew on
`TauCeti.DynkinType`'s pinned Geck-carrier points API. Their Carter and Jantzen references
remain in the carrier modules, where they describe the underlying group constructions.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe v w z

/-- A matrix subgroup over a value ring, presented by an integral Hopf ideal. -/
abbrev IntegralPointsPresentation (n : ℕ)
    (I : HopfIdeal ℤ (coordinateHopfAlgebra ℤ n)) (A : Type v) [CommRing A] :=
  {subgroup : Subgroup (Matrix.GeneralLinearGroup (Fin n) A) //
    subgroup = hopfIdealPointsSubgroup n I A}

namespace IntegralPointsPresentation

noncomputable section

variable {n : ℕ} {I : HopfIdeal ℤ (coordinateHopfAlgebra ℤ n)}
variable {A : Type v} {B : Type w} {C : Type z}
variable [CommRing A] [CommRing B] [CommRing C]

/-- The map of presented points induced by a homomorphism of value rings. -/
def map (P : IntegralPointsPresentation n I A) (Q : IntegralPointsPresentation n I B)
    (f : A →+* B) : P.val →* Q.val :=
  mapHopfIdealPointsSubgroupCongr n I P.property Q.property f.toIntAlgHom

/-- The map of presented points is the entrywise matrix map. -/
@[simp]
theorem coe_map (P : IntegralPointsPresentation n I A) (Q : IntegralPointsPresentation n I B)
    (f : A →+* B) (g : P.val) :
    (P.map Q f g : Matrix.GeneralLinearGroup (Fin n) B) =
      Matrix.GeneralLinearGroup.map f g := by
  simp [map]

/-- The induced map applies the value-ring homomorphism to each matrix coefficient. -/
theorem coe_map_apply (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (f : A →+* B) (g : P.val) (i j : Fin n) :
    ((P.map Q f g : Matrix.GeneralLinearGroup (Fin n) B) : Matrix (Fin n) (Fin n) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := by
  rw [coe_map, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on presented points. -/
@[simp]
theorem map_id (P : IntegralPointsPresentation n I A) :
    P.map P (RingHom.id A) = MonoidHom.id _ := by
  simp [map]

/-- Maps of presented points compose through any presentation of the intermediate point group.

The intermediate presentation `Q` occurs only on the right, so `simp` cannot infer it. Use
this theorem explicitly, supplying `Q`, rather than as a simplification rule. -/
theorem map_comp (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (S : IntegralPointsPresentation n I C)
    (f : A →+* B) (g : B →+* C) :
    P.map S (g.comp f) = (Q.map S g).comp (P.map Q f) := by
  simp only [map, RingHom.toIntAlgHom_comp]
  exact mapHopfIdealPointsSubgroupCongr_comp n I
    P.property Q.property S.property f.toIntAlgHom g.toIntAlgHom

/-- An injective homomorphism of value rings induces an injective map of presented points. -/
theorem map_injective (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (P.map Q f) :=
  mapHopfIdealPointsSubgroupCongr_injective n I P.property Q.property
    (φ := f.toIntAlgHom) (by rwa [RingHom.toIntAlgHom_coe])

section Representation

variable {A B : CommAlgCat.{v} ℤ}

/-- At a bundled value algebra, the presentation agrees with its given algebra structure. -/
private theorem subgroup_eq_bundled (P : IntegralPointsPresentation n I A) :
    P.val = hopfIdealPointsSubgroup n I A := by
  rw [P.property]
  congr 1
  exact Subsingleton.elim _ _

/-- Quotient coordinate-algebra points are the presented matrix points. -/
def mulEquiv (P : IntegralPointsPresentation n I A) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) A ≃*
      P.val :=
  (hopfIdealPointsSubgroupMulEquiv n I A).trans
    (MulEquiv.subgroupCongr P.subgroup_eq_bundled).symm

/-- A quotient point is its underlying general-linear point read as a matrix. -/
@[simp]
theorem coe_mulEquiv_apply (P : IntegralPointsPresentation n I A)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) A) :
    (P.mulEquiv q : Matrix.GeneralLinearGroup (Fin n) A) =
      pointsMulEquiv n (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra ℤ n) I A q) := by
  simp only [mulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact coe_hopfIdealPointsSubgroupMulEquiv_apply n I A q

/-- The inverse representing equivalence recovers the ambient point of the underlying matrix. -/
@[simp]
theorem quotientPointsHom_mulEquiv_symm (P : IntegralPointsPresentation n I A)
    (g : P.val) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra ℤ n) I A (P.mulEquiv.symm g) =
      (pointsMulEquiv (R := ℤ) n).symm (g : Matrix.GeneralLinearGroup (Fin n) A) := by
  simp only [mulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm, MulEquiv.subgroupCongr_apply]

/-- The representing equivalence is natural in the value algebra.

The source presentation occurs only on the right, so this is not a simplification rule. -/
theorem mulEquiv_mapPoints (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) A) :
    Q.mulEquiv
        (HopfAlgebra.mapPoints (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) f q) =
      P.map Q f.hom (P.mulEquiv q) := by
  apply Subtype.ext
  rw [coe_map]
  simp only [mulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (hopfIdealPointsSubgroupMulEquiv_mapPoints n I f q)).trans
    (coe_mapHopfIdealPointsSubgroup n I f.hom _)

end Representation

section Functor

variable (P : ∀ (A : Type v) [CommRing A], IntegralPointsPresentation n I A)

/-- A family of presentations gives a group-valued functor on commutative integer algebras. -/
def functor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (P A).val
  map f := GrpCat.ofHom ((P _).map (P _) f.hom.toRingHom)
  map_id A := congrArg GrpCat.ofHom ((P A).map_id)
  map_comp f g := congrArg GrpCat.ofHom
    ((P _).map_comp (P _) (P _) f.hom.toRingHom g.hom.toRingHom)

/-- The object part is the chosen subgroup of matrices. -/
@[simp]
theorem functor_obj (A : CommAlgCat.{v} ℤ) :
    (functor P).obj A = GrpCat.of (P A).val :=
  (rfl)

/-- The morphism part is the map of presented points. -/
@[simp]
theorem functor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    (functor P).map f = eqToHom (functor_obj P A) ≫
      GrpCat.ofHom ((P A).map (P B) f.hom) ≫ eqToHom (functor_obj P B).symm :=
  (rfl)

/-- The quotient coordinate Hopf algebra represents a family of presented matrix point groups. -/
def natIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) ≅ functor P :=
  NatIso.ofComponents (fun A => (P A).mulEquiv.toGrpIso)
    (by
      intro A B f
      ext q
      exact (P A).mulEquiv_mapPoints (P B) f q)

/-- The forward component of the representing isomorphism is the pointwise equivalence. -/
@[simp]
theorem natIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra ℤ n) I) A) :
    eqToHom (functor_obj P A) ((natIso P).hom.app A q) = (P A).mulEquiv q :=
  (rfl)

/-- The inverse component of the representing isomorphism is the inverse pointwise equivalence. -/
@[simp]
theorem natIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : (P A).val) :
    (natIso P).inv.app A (eqToHom (functor_obj P A).symm g) = (P A).mulEquiv.symm g :=
  (rfl)

end Functor

end

end IntegralPointsPresentation

end TauCeti.GeneralLinear
