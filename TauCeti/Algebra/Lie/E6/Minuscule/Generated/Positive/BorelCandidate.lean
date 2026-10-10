/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E6.Minuscule.PositiveSubsystem.Basic
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular

/-!
# A Borel candidate in the generated E₆ minuscule group

The positive subgroup generated over any field by the six positive numbered roots and the
weight torus is a Borel candidate: it is smooth, geometrically connected and geometrically
solvable. The raising operators are upper triangular in the ordered minuscule basis, and the
torus is diagonal, so the positive subgroup lies scheme-theoretically in the upper-triangular
subgroup of `GL₂₇`.

`isBorelCandidate_carrierDefiningIdeal` expresses this result inside the full generated
minuscule carrier. Maximality among smooth connected solvable subgroups is not asserted.
Neither the generated carrier nor this subgroup is identified with the pinned simply connected
E₆ group or its Borel.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 26–28.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.

The scheme-theoretic triangularity and quotient transport follow
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.BorelCandidate`. The weight-order
argument is supplied by `TauCeti.E6Minuscule.positiveRootWeight_strict`.
-/

public section

open CategoryTheory WithConv
open TauCeti.GeneralLinear.UpperTriangular
  (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra)
attribute [local instance high] Algebra.toModule

namespace TauCeti.E6Minuscule

universe u

namespace Generated.Positive

noncomputable section

variable (A : Type u) [CommRing A]

/-- The generated positive subgroup lies scheme-theoretically in the upper-triangular subgroup. -/
theorem upperTriangular_le_definingIdeal :
    GeneralLinear.UpperTriangular.definingHopfIdeal A 27 ≤ definingIdeal A := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    let B := AdditiveGroup.coordinateHopfAlgebra A
    let q : HopfAlgebra.points (R := A) (H := B) (CommAlgCat.of A B) :=
      toConv (AlgHom.id A B)
    have h :=
      pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
        A (.inl i) (CommAlgCat.of A B) q
    have hpoint : GeneralLinear.pointToGeneralLinear 27
        (toConv (generatorCoordinateMap A (.inl (.inl i))).hom.toAlgHom) =
        (rootSubgroupPoints (.inl i) B (AdditiveGroup.gaPointsMulEquiv q) :
          Matrix.GeneralLinearGroup (Fin 27) B) := by
      rw [generatorCoordinateMap_inl,
        ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap]
      simpa only [AlgHom.mapDomain_apply, q, B, ofConv_toConv, AlgHom.id_comp,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom] using h
    rw [hpoint]
    exact isUpperTriangular_rootSubgroupPoints_inl i B (AdditiveGroup.gaPointsMulEquiv q)
  · apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker
    intro i j hji
    rw [generatorCoordinateMap_inr]
    rw [GeneralLinear.hom_weightTorusBaseChangeCoordinateMap, BialgHom.coe_toAlgHom]
    simpa only [hji.ne', ↓reduceIte] using
      GeneralLinear.weightTorusCoordinateBialgHom_X (S := A) weightTable.weight i j

variable (k : Type u) [Field k]

/-- The positive subgroup has solvable geometric points over any field. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (CommHopfAlgCat.quotientMapOfLe _ (upperTriangular_le_definingIdeal k))
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k 27)

/-- The positive subgroup of the generated E₆ minuscule carrier is a Borel candidate over every
field: smooth, geometrically connected and geometrically solvable. -/
theorem isBorelCandidate_carrierDefiningIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k))
      (carrierDefiningIdeal k) := by
  let e : (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra k))
      (carrierDefiningIdeal k)).obj ≅ coordinateHopfAlgebra k := by
    rw [carrierDefiningIdeal_def]
    exact CommHopfAlgCat.quotientKerOfSurjectiveIso (restriction k) (restriction_surjective k)
  exact HopfIdeal.IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty k).prop_of_iso e.symm (smooth_coordinateHopfAlgebra k))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallyConnected_coordinateHopfAlgebra k))
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallySolvablePoints_coordinateHopfAlgebra k))

end

end Generated.Positive

end TauCeti.E6Minuscule
