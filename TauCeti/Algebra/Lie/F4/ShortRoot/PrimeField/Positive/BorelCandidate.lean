/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Positive.Basic

/-!
# The positive short-root F₄ subgroup over 𝔽₂ is a Borel candidate

In the weight basis of the twenty-six-dimensional module, each raising generator `Eᵢ` sends a
basis vector to a multiple of a basis vector of no larger index, and so does its divided square
`Eᵢ⁽²⁾`, while the weight torus is diagonal. So the positive simple-root subgroups, whose points
are `1 + u Eᵢ + u² Eᵢ⁽²⁾`, and the weight torus lie in the upper-triangular subgroup of `GL₂₆`, and
hence so does the positive subgroup they generate. Its geometric points are therefore solvable.

Cut out inside the carrier's coordinate algebra, the positive subgroup is thus smooth,
geometrically connected and geometrically solvable: it is a Borel candidate, and by
`TauCeti.HopfIdeal.IsBorelCandidate.baseChange` it stays one on every geometric fiber. Maximality
among Borel candidates is not asserted here, nor is any identification of the carrier with an
independently pinned simply connected group scheme.

## Main results

* `TauCeti.F4ShortRoot.PrimeField.isUpperTriangular_rootSubgroupPoints_inl` and
  `TauCeti.F4ShortRoot.PrimeField.isUpperTriangular_weightTorusPoints`: the positive generators
  are upper triangular on points.
* `TauCeti.F4ShortRoot.PrimeField.Positive.upperTriangular_le_definingIdeal`: the positive
  subgroup lies in the upper-triangular subgroup of `GL₂₆`.
* `TauCeti.F4ShortRoot.PrimeField.Positive.geometricallySolvablePoints_coordinateHopfAlgebra`: the
  positive subgroup has solvable geometric points.
* `TauCeti.F4ShortRoot.PrimeField.positiveDefiningIdeal`: the Hopf ideal of the positive subgroup
  in the carrier's coordinate algebra.
* `TauCeti.F4ShortRoot.PrimeField.isBorelCandidate_positiveDefiningIdeal`: the positive subgroup
  is a Borel candidate of the carrier.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 21.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.

The argument follows the positive short-root type-`G₂` subgroup in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.BorelCandidate`; the weight basis of the
twenty-six-dimensional module is already ordered so that raising never increases the index, so no
reordering is needed.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.F4ShortRoot.PrimeField

universe v

noncomputable section

/-- A positive numbered simple-root point of the carrier is an upper-triangular matrix. -/
theorem isUpperTriangular_rootSubgroupPoints_inl (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (u : Multiplicative A) :
    ((rootSubgroupPoints (.inl i) A u : Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A).IsUpperTriangular := by
  rw [coe_rootSubgroupPoints, _root_.TauCeti.F4ShortRoot.coe_rootSubgroupPoints_inl]
  intro a b (hba : b < a)
  -- In the weight basis neither `Eᵢ` nor `Eᵢ⁽²⁾` raises the index of a basis vector.
  have hraise : raisingTarget i b ≠ a :=
    ((by decide : ∀ i b, raisingTarget i b ≤ b) i b |>.trans_lt hba).ne
  have hsquare : raisingDividedSquareTarget i b ≠ a :=
    ((by decide : ∀ i b, raisingDividedSquareTarget i b ≤ b) i b |>.trans_lt hba).ne
  simp [Matrix.one_apply_ne hba.ne', raisingMatrix_apply, raisingDividedSquareMatrix_apply,
    hraise.symm, hsquare.symm]

/-- A weight-torus point of the carrier is an upper-triangular matrix. -/
theorem isUpperTriangular_weightTorusPoints (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (s : Fin 4 → Aˣ) :
    ((weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A).IsUpperTriangular := by
  rw [coe_weightTorusPoints, _root_.TauCeti.F4ShortRoot.coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  exact Matrix.blockTriangular_diagonal _

namespace Positive

/-- **The positive subgroup is upper triangular**: the upper-triangular subgroup of `GL₂₆`
contains it, which on Hopf ideals is the reverse inclusion. -/
theorem upperTriangular_le_definingIdeal :
    GeneralLinear.UpperTriangular.definingHopfIdeal (ZMod 2) 26 ≤ definingIdeal := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    let q : HopfAlgebra.points (R := ZMod 2)
        (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
        (CommAlgCat.of (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) :=
      toConv (AlgHom.id (ZMod 2) _)
    have h := isUpperTriangular_rootSubgroupPoints_inl i _
      (AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) q)
    have hq : (CommHopfAlgCat.mapPointsFunctor (PrimeField.generator (.inl (.inl i)))).app _ q =
        toConv (PrimeField.generator (.inl (.inl i))).hom.toAlgHom := by
      apply WithConv.ofConv_injective
      exact AlgHom.ext fun x ↦ CommHopfAlgCat.mapPointsFunctor_app_apply_apply _ _ q x
    rw [coe_rootSubgroupPoints_gaPointsMulEquiv, hq, GeneralLinear.pointsMulEquiv_apply] at h
    exact h
  · apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    let q : HopfAlgebra.points (R := ZMod 2)
        (H := (DiagonalizableGroup.coordinateRing (ZMod 2)
          (SplitTorus.characterGroup (Fin 4))).obj)
        (CommAlgCat.of (ZMod 2) (DiagonalizableGroup.coordinateRing (ZMod 2)
          (SplitTorus.characterGroup (Fin 4))).obj) :=
      toConv (AlgHom.id (ZMod 2) _)
    have h := isUpperTriangular_weightTorusPoints _ (SplitTorus.pointsMulEquiv q)
    have hq : (CommHopfAlgCat.mapPointsFunctor (PrimeField.generator (.inr ()))).app _ q =
        toConv (PrimeField.generator (.inr ())).hom.toAlgHom := by
      apply WithConv.ofConv_injective
      exact AlgHom.ext fun x ↦ CommHopfAlgCat.mapPointsFunctor_app_apply_apply _ _ q x
    rw [coe_weightTorusPoints_pointsMulEquiv, hq, GeneralLinear.pointsMulEquiv_apply] at h
    exact h

open GeneralLinear.UpperTriangular in
/-- **The positive subgroup has solvable geometric points**, since they embed into the
upper-triangular point group of `GL₂₆`. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty (ZMod 2) coordinateHopfAlgebra :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective (ZMod 2)
    (CommHopfAlgCat.quotientMapOfLe _ upperTriangular_le_definingIdeal)
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra (ZMod 2) 26)

end Positive

/-- Restriction of carrier coordinates to the positive subgroup. -/
abbrev positiveRestriction :
    finiteTypeCoordinateHopfAlgebra.obj ⟶ Positive.coordinateHopfAlgebra :=
  CommHopfAlgCat.quotientMapOfLe _ Positive.carrierDefiningIdeal_le

/-- The Hopf ideal of the positive subgroup inside the carrier's coordinate algebra: the kernel of
restriction to the positive subgroup. -/
def positiveDefiningIdeal : HopfIdeal (ZMod 2) finiteTypeCoordinateHopfAlgebra :=
  HopfIdeal.kerOfSurjective positiveRestriction.hom
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _)

/-- A carrier coordinate lies in the positive ideal exactly when it vanishes on the positive
subgroup. -/
@[simp]
theorem mem_positiveDefiningIdeal (x : finiteTypeCoordinateHopfAlgebra) :
    x ∈ positiveDefiningIdeal ↔ positiveRestriction.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective _ _

/-- **The positive subgroup is a Borel candidate of the carrier**: smooth, geometrically
connected, and with solvable geometric points. By
`TauCeti.HopfIdeal.IsBorelCandidate.baseChange` it remains one after extension to any field of
characteristic two. -/
theorem isBorelCandidate_positiveDefiningIdeal :
    HopfIdeal.IsBorelCandidate (ZMod 2) finiteTypeCoordinateHopfAlgebra positiveDefiningIdeal := by
  -- The quotient is the positive subgroup's coordinate algebra.
  let e : (FiniteTypeCommHopfAlgCat.quotient finiteTypeCoordinateHopfAlgebra
        positiveDefiningIdeal).obj ≅ Positive.coordinateHopfAlgebra :=
    CommHopfAlgCat.quotientKerOfSurjectiveIso positiveRestriction
      (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
  refine HopfIdeal.IsBorelCandidate.mk ?_ ?_ ?_
  · exact (smoothCommHopfAlgProperty (ZMod 2)).prop_of_iso e.symm
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  · exact (geometricallyConnectedCommHopfAlgProperty (ZMod 2)).prop_of_iso e.symm
      Positive.geometricallyConnected_coordinateHopfAlgebra
  · exact (geometricallySolvablePointsCommHopfAlgProperty (ZMod 2)).prop_of_iso e.symm
      Positive.geometricallySolvablePoints_coordinateHopfAlgebra

end

end TauCeti.F4ShortRoot.PrimeField
