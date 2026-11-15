/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Triangular.Basic

/-!
# Solvability of the positive Geck carrier after base change

The integral positive Geck carrier embeds into an upper-triangular group, so its points over every
commutative ring form a solvable group. Transport through the existing base-change coordinate
isomorphism gives the same conclusion for the positive carrier over any new base ring. In
particular, over a field it satisfies the geometric-points solvability property.
-/

public section

namespace TauCeti.DynkinType

universe u v

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- Every point group of the base-changed positive Geck carrier is solvable. The base ring and the
value algebra may lie in different universes. -/
theorem isSolvable_points_geckTorusPositiveBaseChange
    (R : Type u) [CommRing R] (A : CommAlgCat.{v} R) :
    Group.IsSolvable
      (HopfAlgebra.points (R := R)
        (H := CommHopfAlgCat.quotient
          (CommHopfAlgCat.baseChange (K := R)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht R)) A) := by
  let e := CommHopfAlgCat.baseChangeIsoPointsMulEquiv
    (t.geckTorusPositiveBaseChangeCoordinateIso ht R) A
  let _ := t.isSolvable_points_geckTorusPositive ht
    (CommAlgCat.restrictScalarsObj (algebraMap ℤ R) A)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Over every field, the positive Geck carrier has solvable geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_geckTorusPositiveBaseChange
    (k : Type u) [Field k] :
    geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := k)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht k)) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact t.isSolvable_points_geckTorusPositiveBaseChange ht k
    (CommAlgCat.of k (AlgebraicClosure k))

end

end TauCeti.DynkinType
