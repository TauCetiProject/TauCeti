/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Reductive

/-!
# The positive short-root G₂ subgroup over 𝔽₃ is a Borel candidate

In the weight basis of the seven-dimensional module, listed in decreasing order, the raising
generators are supported on the superdiagonal and the divided square of the short one lies above
the diagonal, while the weight torus is diagonal. So the positive simple-root subgroups and the
weight torus lie in the upper-triangular subgroup of `GL₇`, and hence so does the positive
subgroup they generate. Its geometric points are therefore solvable.

Cut out inside the carrier's coordinate algebra, the positive subgroup is thus smooth,
geometrically connected and geometrically solvable: it is a Borel candidate, and by
`TauCeti.HopfIdeal.IsBorelCandidate.baseChange` it stays one on every geometric fiber. It also
contains the chosen split maximal torus. These are the conditions a pinning places on its Borel
subgroup apart from maximality among Borel candidates, which is not asserted here, nor is any
identification of the carrier with an independently pinned simply connected group scheme.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.Positive.upperTriangular_le_definingIdeal`: the positive
  subgroup lies in the upper-triangular subgroup of `GL₇`.
* `TauCeti.G2ShortRoot.PrimeField.Positive.geometricallySolvablePoints_coordinateHopfAlgebra`: the
  positive subgroup has solvable geometric points.
* `TauCeti.G2ShortRoot.PrimeField.positiveDefiningIdeal`: the Hopf ideal of the positive subgroup
  in the carrier's coordinate algebra.
* `TauCeti.G2ShortRoot.PrimeField.positiveDefiningIdeal_le_splitMaximalTorus_definingIdeal`: the
  positive subgroup contains the chosen split maximal torus.
* `TauCeti.G2ShortRoot.PrimeField.isBorelCandidate_positiveDefiningIdeal`: the positive subgroup
  is a Borel candidate of the carrier.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 21.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.

The triangularity argument follows the positive Geck carrier in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Triangular.Basic`;
here the weight basis is already in decreasing order, so no reordering is needed.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.G2ShortRoot.PrimeField

universe v

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A positive numbered simple-root point of the carrier is an upper-triangular matrix. -/
theorem isUpperTriangular_rootSubgroupPoints_inl (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((rootSubgroupPoints (.inl i) A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A).IsUpperTriangular := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints, rootMatrix_inl,
    rootDividedSquareMatrix_inl]
  intro a b (hba : b < a)
  have hab : a ≠ b := (ne_of_lt hba).symm
  rw [Fin.lt_def] at hba
  have hsuper : (b : ℕ) ≠ a + 1 := by omega
  have hsquare : ¬(2 = (a : ℕ) ∧ 4 = (b : ℕ)) := by omega
  fin_cases i <;>
  simp [Matrix.one_apply_ne hab, raisingMatrix_apply, Fin.ext_iff, hsuper, hsquare]

/-- A weight-torus point of the carrier is an upper-triangular matrix. -/
theorem isUpperTriangular_weightTorusPoints (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (s : Fin 2 → Aˣ) :
    ((weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A).IsUpperTriangular := by
  rw [coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal]
  exact Matrix.blockTriangular_diagonal _

namespace Positive

/-- **The positive subgroup is upper triangular**: the upper-triangular subgroup of `GL₇`
contains it, which on Hopf ideals is the reverse inclusion. -/
theorem upperTriangular_le_definingIdeal :
    GeneralLinear.UpperTriangular.definingHopfIdeal (ZMod 3) 7 ≤ definingIdeal := by
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    let q : HopfAlgebra.points (R := ZMod 3)
        (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
        (CommAlgCat.of (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) :=
      toConv (AlgHom.id (ZMod 3) _)
    have h := isUpperTriangular_rootSubgroupPoints_inl i _
      (AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) q)
    have hq : (CommHopfAlgCat.mapPointsFunctor (PrimeField.generator (.inl (.inl i)))).app _ q =
        toConv (PrimeField.generator (.inl (.inl i))).hom.toAlgHom := by
      apply WithConv.ofConv_injective
      exact AlgHom.ext fun x ↦ CommHopfAlgCat.mapPointsFunctor_app_apply_apply _ _ q x
    rw [coe_rootSubgroupPoints_gaPointsMulEquiv, hq, GeneralLinear.pointsMulEquiv_apply] at h
    exact h
  · apply GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    let q : HopfAlgebra.points (R := ZMod 3)
        (H := (DiagonalizableGroup.coordinateRing (ZMod 3)
          (SplitTorus.characterGroup (Fin 2))).obj)
        (CommAlgCat.of (ZMod 3) (DiagonalizableGroup.coordinateRing (ZMod 3)
          (SplitTorus.characterGroup (Fin 2))).obj) :=
      toConv (AlgHom.id (ZMod 3) _)
    have h := isUpperTriangular_weightTorusPoints _ (SplitTorus.pointsMulEquiv q)
    have hq : (CommHopfAlgCat.mapPointsFunctor (PrimeField.generator (.inr ()))).app _ q =
        toConv (PrimeField.generator (.inr ())).hom.toAlgHom := by
      apply WithConv.ofConv_injective
      exact AlgHom.ext fun x ↦ CommHopfAlgCat.mapPointsFunctor_app_apply_apply _ _ q x
    rw [coe_weightTorusPoints_pointsMulEquiv, hq, GeneralLinear.pointsMulEquiv_apply] at h
    exact h

open GeneralLinear.UpperTriangular in
/-- **The positive subgroup has solvable geometric points**, since they embed into the
upper-triangular point group of `GL₇`. -/
theorem geometricallySolvablePoints_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty (ZMod 3) coordinateHopfAlgebra :=
  geometricallySolvablePointsCommHopfAlgProperty_of_surjective (ZMod 3)
    (CommHopfAlgCat.quotientMapOfLe _ upperTriangular_le_definingIdeal)
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra (ZMod 3) 7)

end Positive

/-- Restriction of carrier coordinates to the positive subgroup. -/
abbrev positiveRestriction : carrierAlgebra ⟶ Positive.coordinateHopfAlgebra :=
  CommHopfAlgCat.quotientMapOfLe _ Positive.carrierDefiningIdeal_le

/-- The Hopf ideal of the positive subgroup inside the carrier's coordinate algebra: the kernel of
restriction to the positive subgroup. -/
def positiveDefiningIdeal : HopfIdeal (ZMod 3) carrierAlgebra :=
  HopfIdeal.kerOfSurjective positiveRestriction.hom
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _)

/-- A carrier coordinate lies in the positive ideal exactly when it vanishes on the positive
subgroup. -/
@[simp]
theorem mem_positiveDefiningIdeal (x : carrierAlgebra) :
    x ∈ positiveDefiningIdeal ↔ positiveRestriction.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective _ _

/-- **The positive subgroup contains the chosen split maximal torus.** -/
theorem positiveDefiningIdeal_le_splitMaximalTorus_definingIdeal :
    positiveDefiningIdeal ≤ splitMaximalTorus.definingIdeal := by
  rw [splitMaximalTorus_definingIdeal]
  intro x hx
  rw [mem_positiveDefiningIdeal] at hx
  rw [← HopfIdeal.mem_toIdeal, weightTorusDefiningIdeal_toIdeal, RingHom.mem_ker]
  have hcomp : positiveRestriction ≫
      CommHopfAlgCat.commonKernelLift Positive.generator (.inr ()) = weightTorusCoordinateMap := by
    apply (cancel_epi (CommHopfAlgCat.mkQuotient _ _)).1
    rw [CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, Positive.generator_inr]
  rw [← hcomp, CommHopfAlgCat.comp_apply, hx, map_zero]

/-- **The positive subgroup is a Borel candidate of the carrier**: smooth, geometrically
connected, and with solvable geometric points. By
`TauCeti.HopfIdeal.IsBorelCandidate.baseChange` it remains one after extension to any field of
characteristic three. -/
theorem isBorelCandidate_positiveDefiningIdeal :
    HopfIdeal.IsBorelCandidate (ZMod 3) finiteTypeCarrierAlgebra positiveDefiningIdeal := by
  -- The quotient is the positive subgroup's coordinate algebra.
  let e : (FiniteTypeCommHopfAlgCat.quotient finiteTypeCarrierAlgebra positiveDefiningIdeal).obj ≅
      Positive.coordinateHopfAlgebra :=
    CommHopfAlgCat.quotientKerOfSurjectiveIso positiveRestriction
      (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
  refine HopfIdeal.IsBorelCandidate.mk ?_ ?_ ?_
  · exact (smoothCommHopfAlgProperty (ZMod 3)).prop_of_iso e.symm
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  · exact (geometricallyConnectedCommHopfAlgProperty (ZMod 3)).prop_of_iso e.symm
      Positive.geometricallyConnected_coordinateHopfAlgebra
  · exact (geometricallySolvablePointsCommHopfAlgProperty (ZMod 3)).prop_of_iso e.symm
      Positive.geometricallySolvablePoints_coordinateHopfAlgebra

end

end TauCeti.G2ShortRoot.PrimeField
