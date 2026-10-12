/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Group
public import TauCeti.AlgebraicTopology.UniversalCover.SemilocallySimplyConnected
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Projection
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SimplyConnected

/-!
# The compact Spin group as a universal covering group

For `n ≥ 3`, the compact real Spin group is simply connected and its projection to the
positive-definite special orthogonal group is a covering homomorphism. Consequently it is the
universal covering group of `SO(n)`. This file identifies it with the path-class construction
`UniversalCover 1` by a continuous multiplicative equivalence commuting with both projections.

The dimension bound excludes `Spin(2)`, which is a circle and is not simply connected. The result
is topological; it makes no assertion about algebraic simple connectedness of complex Spin groups.

## Main definitions

* `CliffordAlgebra.realCliffordSpinUniversalCoverEquivZero`: the continuous group equivalence
  from compact `Spin(n)` to the universal cover of compact `SO(n)`, for `n ≥ 3`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (2015), Chapter 5.
-/

public section
noncomputable section

open scoped Manifold

namespace CliffordAlgebra

open TauCeti

local instance realCliffordSpinLocallyPathConnectedSpace (n : ℕ) :
    LocallyPathConnectedSpace (realCliffordSpinGroupZero n) := by
  let _ : LocallyPathConnectedSpace
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :=
    ChartedSpace.locallyPathConnectedSpace
      (LieSubalgebra.toSubmodule (Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, _root_.CliffordAlgebra (realCliffordForm n 0)))
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)))))
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)))
  exact (TauCeti.CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange n).symm.toHomeomorph
    |>.locallyPathConnectedSpace

local instance realSpecialOrthogonalLocallyPathConnectedSpace (n : ℕ) [NeZero n] :
    LocallyPathConnectedSpace
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :=
  ((isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).isQuotientMap
    (realCliffordSpinDoubleCoverZero n).rightHom_surjective).locallyPathConnectedSpace

local instance realSpecialOrthogonalSemilocallySimplyConnectedSpace (n : ℕ) [NeZero n]
    [SimplyConnectedSpace (realCliffordSpinGroupZero n)] :
    SemilocallySimplyConnectedSpace
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :=
  SemilocallySimplyConnectedSpace.of_isCoveringMap
    (isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n)
    (realCliffordSpinDoubleCoverZero n).rightHom_surjective

/-- For `n ≥ 3`, compact `Spin(n)` is continuously isomorphic to the universal covering group of
compact `SO(n)`. Under this equivalence, the endpoint projection is the existing concrete Spin
projection. -/
noncomputable def realCliffordSpinUniversalCoverEquivZero (n : ℕ) (hn : 3 ≤ n) :
    realCliffordSpinGroupZero n ≃ₜ*
      UniversalCover
        (1 : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) :=
    simplyConnectedSpace_realCliffordSpinGroupZero n hn
  exact IsCoveringMap.continuousMulEquivUniversalCover
    (p := realCliffordSpinProjectionZero n)
    (isCoveringMap_realCliffordSpinProjectionZero n)

/-- The universal-cover projection after the compact Spin comparison is the concrete Spin
projection. -/
@[simp]
theorem projHom_comp_realCliffordSpinUniversalCoverEquivZero
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    UniversalCover.projHom.comp
      (realCliffordSpinUniversalCoverEquivZero n hn :
        realCliffordSpinGroupZero n →ₜ*
          UniversalCover
            (1 : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))) =
      realCliffordSpinProjectionZero n := by
  let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) :=
    simplyConnectedSpace_realCliffordSpinGroupZero n hn
  rw [realCliffordSpinUniversalCoverEquivZero]
  exact IsCoveringMap.projHom_comp_continuousMulEquivUniversalCover
    (p := realCliffordSpinProjectionZero n)
    (isCoveringMap_realCliffordSpinProjectionZero n)

/-- Applying the universal-cover projection after the compact Spin comparison gives the concrete
Spin action on the positive-definite quadratic space. -/
@[simp]
theorem realCliffordSpinUniversalCoverEquivZero_apply_proj
    (n : ℕ) (hn : 3 ≤ n) (s : realCliffordSpinGroupZero n) :
    UniversalCover.projHom (realCliffordSpinUniversalCoverEquivZero n hn s) =
      spinToSpecialOrthogonal (realCliffordForm n 0) s := by
  let _ : NeZero n := ⟨by omega⟩
  calc
    UniversalCover.projHom (realCliffordSpinUniversalCoverEquivZero n hn s) =
        realCliffordSpinProjectionZero n s :=
      DFunLike.congr_fun (projHom_comp_realCliffordSpinUniversalCoverEquivZero n hn) s
    _ = spinToSpecialOrthogonal (realCliffordForm n 0) s := by
      rw [realCliffordSpinProjectionZero_apply, realCliffordSpinDoubleCoverZero_rightHom]

/-- Projecting the inverse image of a universal-cover point under the compact Spin comparison
recovers its endpoint in `SO(n)`. -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinUniversalCoverEquivZero_symm_apply
    (n : ℕ) (hn : 3 ≤ n)
    (x : UniversalCover
      (1 : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))) :
    spinToSpecialOrthogonal (realCliffordForm n 0)
        ((realCliffordSpinUniversalCoverEquivZero n hn).symm x) =
      UniversalCover.projHom x := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) :=
    simplyConnectedSpace_realCliffordSpinGroupZero n hn
  rw [realCliffordSpinUniversalCoverEquivZero]
  rw [← realCliffordSpinDoubleCoverZero_rightHom, ← realCliffordSpinProjectionZero_apply]
  exact IsCoveringMap.continuousMulEquivUniversalCover_symm_apply_proj
    (p := realCliffordSpinProjectionZero n)
    (isCoveringMap_realCliffordSpinProjectionZero n) x

end CliffordAlgebra
