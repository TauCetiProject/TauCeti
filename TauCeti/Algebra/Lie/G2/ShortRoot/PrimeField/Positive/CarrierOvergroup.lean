/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.SolvableOvergroup
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Solvable overgroups in the short-root G₂ carrier

The scalar extension of the positive short-root `G₂` subgroup embeds in the scalar-extended
carrier. This file packages its defining ideal in the generated-coordinate presentation and
transports the ambient Lie--Kolchin overgroup theorem to the carrier.

Consequently, over an algebraically closed field of characteristic three, every Borel candidate
in the carrier which contains the positive subgroup pulls back to an upper-triangular subgroup
of `GL₇`. Proving that the positive subgroup is the carrier's upper-triangular intersection will
turn this containment into Borel maximality; that intersection identification is not asserted
here.

## Main declarations

* `generatedPositiveDefiningIdeal`: the positive subgroup's ideal in the generated carrier.
* `upperTriangular_le_comapOfSurjective_of_geometricallySolvable_of_le`: a reduced connected
  solvable carrier overgroup pulls back to an upper-triangular subgroup of `GL₇`.
* `upperTriangular_le_comapOfSurjective_of_isBorelCandidate_of_le`: a Borel candidate containing
  the positive subgroup pulls back to an upper-triangular subgroup of `GL₇`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§17 and 21.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 and §17.a.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField.Positive

noncomputable section

universe u

section ScalarExtension

variable (k : Type u) [CommRing k] [Algebra (ZMod 3) k]

/-- Restriction from the generated scalar extension of the carrier to the scalar extension of
the positive subgroup. -/
def generatedPositiveRestriction :
    generatedCoordinateHopfAlgebra k ⟶
      CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra :=
  (coordinateHopfAlgebraGeneratedIso k).inv ≫
    CommHopfAlgCat.baseChangeMap (K := k) PrimeField.positiveRestriction

/-- The generated carrier's ambient coordinate map followed by positive restriction is the
standard coordinate map of the positive subgroup. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedPositiveRestriction :
    generatedCoordinateMap k ≫ generatedPositiveRestriction k = standardCoordinateMap k := by
  apply (cancel_epi
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 3) k 7).hom).1
  rw [← Category.assoc,
    ← baseChangeMap_carrierQuotient_comp_coordinateHopfAlgebraGeneratedIso_hom k]
  simp only [generatedPositiveRestriction, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← (CommHopfAlgCat.baseChangeFunctor (K := k)).map_comp]
  rw [CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
  rw [standardCoordinateMap_def, Iso.hom_inv_id_assoc]

/-- Restriction from the generated carrier to its positive subgroup is surjective. -/
theorem generatedPositiveRestriction_surjective :
    Function.Surjective (generatedPositiveRestriction k).hom := by
  simpa only [generatedPositiveRestriction, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso PrimeField.positiveRestriction
      (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
      (coordinateHopfAlgebraGeneratedIso k).symm (Iso.refl _)

/-- The defining ideal of the positive subgroup inside the generated scalar extension of the
carrier. -/
def generatedPositiveDefiningIdeal : HopfIdeal k (generatedCoordinateHopfAlgebra k) :=
  HopfIdeal.kerOfSurjective (generatedPositiveRestriction k).hom
    (generatedPositiveRestriction_surjective k)

/-- The generated positive ideal is the kernel of positive restriction. -/
theorem generatedPositiveDefiningIdeal_def :
    generatedPositiveDefiningIdeal k =
      HopfIdeal.kerOfSurjective (generatedPositiveRestriction k).hom
        (generatedPositiveRestriction_surjective k) := (rfl)

/-- Membership in the generated positive ideal is vanishing under positive restriction. -/
@[simp]
theorem mem_generatedPositiveDefiningIdeal (x : generatedCoordinateHopfAlgebra k) :
    x ∈ generatedPositiveDefiningIdeal k ↔ (generatedPositiveRestriction k).hom x = 0 := by
  rw [generatedPositiveDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The inverse image of the positive ideal in ambient `GL₇` is the kernel of the positive
subgroup's standard coordinate map. -/
theorem comapOfSurjective_generatedPositiveDefiningIdeal_eq_ker_standardCoordinateMap :
    (generatedPositiveDefiningIdeal k).comapOfSurjective (generatedCoordinateMap k).hom
        (generatedCoordinateMap_surjective k) =
      HopfIdeal.kerOfSurjective (standardCoordinateMap k).hom
        (standardCoordinateMap_surjective k) := by
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, mem_generatedPositiveDefiningIdeal,
    HopfIdeal.mem_kerOfSurjective, ← CommHopfAlgCat.comp_apply,
    generatedCoordinateMap_comp_generatedPositiveRestriction]

end ScalarExtension

section AlgebraicallyClosed

variable (k : Type u) [Field k] [Algebra (ZMod 3) k] [IsAlgClosed k]

/-- A reduced connected solvable subgroup of the scalar-extended carrier which contains the
positive subgroup pulls back to an upper-triangular subgroup of `GL₇`. -/
theorem upperTriangular_le_comapOfSurjective_of_geometricallySolvable_of_le
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    [IsReduced (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I))
    (hcontain : I ≤ generatedPositiveDefiningIdeal k) :
    GeneralLinear.UpperTriangular.definingHopfIdeal k 7 ≤
      I.comapOfSurjective (generatedCoordinateMap k).hom
        (generatedCoordinateMap_surjective k) := by
  let J := I.comapOfSurjective (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)
  let e := CommHopfAlgCat.Hom.quotientIsoOfSurjective (generatedCoordinateMap k)
    (generatedCoordinateMap_surjective k) I
  let _ : IsReduced
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 7) J) :=
    isReduced_of_injective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  apply upperTriangular_le_of_geometricallySolvable k J
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm hconn)
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm hsolv)
  have hcomap : J ≤ (generatedPositiveDefiningIdeal k).comapOfSurjective
      (generatedCoordinateMap k).hom (generatedCoordinateMap_surjective k) :=
    HopfIdeal.comapOfSurjective_mono (generatedCoordinateMap k).hom
      (generatedCoordinateMap_surjective k) hcontain
  rw [comapOfSurjective_generatedPositiveDefiningIdeal_eq_ker_standardCoordinateMap] at hcomap
  intro x hx
  rw [RingHom.mem_ker]
  exact (HopfIdeal.mem_kerOfSurjective _ _).mp (hcomap hx)

/-- A Borel candidate in the scalar-extended carrier which contains the positive subgroup
pulls back to an upper-triangular subgroup of `GL₇`.

The conclusion is contravariant: the ambient upper-triangular ideal lies below the inverse image
of the candidate ideal. Proving that the positive subgroup is the carrier's upper-triangular
intersection will therefore turn this containment into the maximality required for a Borel. -/
theorem upperTriangular_le_comapOfSurjective_of_isBorelCandidate_of_le
    (I : HopfIdeal k (generatedCoordinateHopfAlgebra k))
    (hI : HopfIdeal.IsBorelCandidate k (finiteTypeGeneratedCoordinateHopfAlgebra k) I)
    (hcontain : I ≤ generatedPositiveDefiningIdeal k) :
    GeneralLinear.UpperTriangular.definingHopfIdeal k 7 ≤
      I.comapOfSurjective (generatedCoordinateMap k).hom
        (generatedCoordinateMap_surjective k) := by
  let _ : IsReduced
      (CommHopfAlgCat.quotient (generatedCoordinateHopfAlgebra k) I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp hI.smooth).isReduced
  exact upperTriangular_le_comapOfSurjective_of_geometricallySolvable_of_le k I
    hI.geometricallyConnected hI.geometricallySolvable hcontain

end AlgebraicallyClosed

end

end TauCeti.G2ShortRoot.PrimeField.Positive
