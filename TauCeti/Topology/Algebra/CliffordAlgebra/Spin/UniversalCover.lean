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
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Connected
import TauCeti.Topology.Homotopy.Covering

/-!
# The compact Spin group as a universal covering group

For `n ≥ 3`, the compact real Spin group is simply connected and its projection to the
positive-definite special orthogonal group is a covering homomorphism. Consequently it is the
universal covering group of `SO(n)`. This file identifies it with the path-class construction
`UniversalCover 1` by a continuous multiplicative equivalence commuting with both projections.

The dimension bound excludes `Spin(2)`, which is a circle and is not simply connected. The result
is topological; it makes no assertion about algebraic simple connectedness of complex Spin groups.

The kernel `{±1}` of a simply connected covering group is the fundamental group of its base, so
`π₁(SO(n), 1)` is cyclic of order two for `n ≥ 3`. Its nontrivial element is the projection to
`SO(n)` of a path from `1` to `-1` in `Spin(n)`. Separately, for every `n ≥ 2` the projection is a
covering map with two-point fibres from a path-connected space, and a path-connected covering space
of a simply connected space is injective over it, so `SO(n)` is not simply connected. Both
statements are transported to the matrix group `Matrix.specialOrthogonalGroup (Fin n) ℝ`; for
`n = 3` this is the classical fact that the rotation group `SO(3)` is not simply connected.

## Main definitions

* `CliffordAlgebra.realCliffordSpinUniversalCoverEquivZero`: the continuous group equivalence
  from compact `Spin(n)` to the universal cover of compact `SO(n)`, for `n ≥ 3`.
* `CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv`: `π₁(SO(n), 1) ≃* ℤ/2` for
  `n ≥ 3`.
* `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv`: the same isomorphism for the matrix
  group `Matrix.specialOrthogonalGroup (Fin n) ℝ`.

## Main statements

* `CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv_symm_ofAdd_one`: the nontrivial
  element of `π₁(SO(n), 1)` is the projection of a path from `1` to `-1` in `Spin(n)`.
* `CliffordAlgebra.not_simplyConnectedSpace_realSpecialOrthogonal`: `SO(n)` is not simply
  connected for `n ≥ 2`.
* `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv_symm_ofAdd_one` and
  `TauCeti.not_simplyConnectedSpace_specialOrthogonalGroup`: the same two facts for the matrix group
  `Matrix.specialOrthogonalGroup (Fin n) ℝ`.

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
  -- Fix the model's norm and normed-space structures first: searching for them inside the
  -- local path-connectedness search exceeds the instance-synthesis budget.
  let _ : SeminormedAddCommGroup
      (LieSubalgebra.toSubmodule (Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, _root_.CliffordAlgebra (realCliffordForm n 0)))
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))))) :=
    inferInstance
  let _ : NormedSpace ℝ
      (LieSubalgebra.toSubmodule (Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, _root_.CliffordAlgebra (realCliffordForm n 0)))
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))))) :=
    inferInstance
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

/-! ### The fundamental group of `SO(n)` -/

/-- **The fundamental group of `SO(n)` is `ℤ/2` for `n ≥ 3`.** The compact Spin group is a simply
connected covering group of the positive-definite special orthogonal group with kernel `{±1}`, so
`π₁(SO(n), 1)` is that kernel. The generator is the projection of a path from `1` to `-1` in
`Spin(n)` (`CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv_symm_ofAdd_one`). -/
noncomputable def realSpecialOrthogonalFundamentalGroupMulEquiv (n : ℕ) (hn : 3 ≤ n) :
    FundamentalGroup (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) 1 ≃*
      Multiplicative (ZMod 2) := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) :=
    simplyConnectedSpace_realCliffordSpinGroupZero n hn
  let S := realCliffordSpinDoubleCoverZero n
  exact ((isCoveringMap_realCliffordSpinProjectionZero n).kerMulEquivFundamentalGroup.symm.trans
    (MulEquiv.subgroupCongr (by
      rw [coeMonoidHom_realCliffordSpinProjectionZero, ← S.range_inl_eq_ker_rightHom]))).trans
    (MonoidHom.ofInjective S.inl_injective).symm

/-- The nontrivial element of `π₁(SO(n), 1)`, `n ≥ 3`, is the class of the loop obtained by
projecting to `SO(n)` any path from `1` to `-1` in the compact Spin group. -/
theorem realSpecialOrthogonalFundamentalGroupMulEquiv_symm_ofAdd_one (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) (γ : Path 1
      (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero)) :
    (realSpecialOrthogonalFundamentalGroupMulEquiv n hn).symm (Multiplicative.ofAdd 1) =
      FundamentalGroup.fromPath (.mk ((γ.map (realCliffordSpinProjectionZero n).continuous).cast
        (map_one (realCliffordSpinProjectionZero n)).symm
        (realCliffordSpinProjectionZero_negOne n).symm)) := by
  let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) :=
    simplyConnectedSpace_realCliffordSpinGroupZero n hn
  have hmem :
      spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero ∈
        (realCliffordSpinProjectionZero n : realCliffordSpinGroupZero n →*
          QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).ker :=
    MonoidHom.mem_ker.mpr (realCliffordSpinProjectionZero_negOne n)
  rw [← (isCoveringMap_realCliffordSpinProjectionZero n).kerMulEquivFundamentalGroup_apply
    ⟨_, hmem⟩ γ]
  simp only [realSpecialOrthogonalFundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm]
  congr 1
  exact Subtype.ext (by simp [MonoidHom.ofInjective_apply])

/-- **`SO(n)` is not simply connected for `n ≥ 2`.** The compact Spin group is a path-connected
covering space of the positive-definite special orthogonal group whose fibres have two points,
whereas a path-connected covering space of a simply connected space is injective over it. -/
theorem not_simplyConnectedSpace_realSpecialOrthogonal (n : ℕ) (hn : 2 ≤ n) :
    ¬ SimplyConnectedSpace (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) := by
  intro _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have := pathConnectedSpace_realCliffordSpinGroupZero_add_two m
  let S := realCliffordSpinDoubleCoverZero (m + 2)
  have hne : S.inl (Multiplicative.ofAdd 1) ≠ S.inl 1 := S.inl_injective.ne (by decide)
  refine hne ((isCoveringMap_realCliffordSpinProjectionZero (m + 2)).injective ?_)
  simp [S]

end CliffordAlgebra

namespace TauCeti

/-- **The fundamental group of the matrix group `SO(n)` is `ℤ/2` for `n ≥ 3`.** The real
special-orthogonal matrices form a topological group isomorphic to the special orthogonal group of
`realCliffordForm n 0`, whose fundamental group is computed by
`CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv`. The generator is described by
`TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv_symm_ofAdd_one`. -/
noncomputable def specialOrthogonalGroupFundamentalGroupMulEquiv (n : ℕ) (hn : 3 ≤ n) :
    FundamentalGroup (Matrix.specialOrthogonalGroup (Fin n) ℝ) 1 ≃* Multiplicative (ZMod 2) :=
  (FundamentalGroup.homeomorphMulEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n).toHomeomorph
    (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n))).trans
    (_root_.CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv n hn)

/-- The nontrivial element of `π₁(SO(n), 1)` for the matrix group, `n ≥ 3`, is the class of the
loop of matrices obtained from any path from `1` to `-1` in the compact Spin group by projecting
to the special orthogonal group of `realCliffordForm n 0` and passing to matrices. -/
theorem specialOrthogonalGroupFundamentalGroupMulEquiv_symm_ofAdd_one (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) (γ : Path 1 (_root_.CliffordAlgebra.spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero)) :
    (specialOrthogonalGroupFundamentalGroupMulEquiv n hn).symm (Multiplicative.ofAdd 1) =
      FundamentalGroup.fromPath (.mk ((γ.map
        ((QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n).symm.continuous
          |>.comp (_root_.CliffordAlgebra.realCliffordSpinProjectionZero n).continuous)).cast
        (by simp) (by simp))) := by
  rw [specialOrthogonalGroupFundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    _root_.CliffordAlgebra.realSpecialOrthogonalFundamentalGroupMulEquiv_symm_ofAdd_one n hn γ,
    FundamentalGroup.homeomorphMulEquivOfEq_symm_apply, FundamentalGroup.mapOfEq_apply]
  -- Both sides are the class of the loop `t ↦ g⁻¹ (π (γ t))`, for `g` the matrix comparison and
  -- `π` the Spin projection; the endpoint casts differ only in their proofs.
  rfl

/-- **The matrix group `SO(n)` is not simply connected for `n ≥ 2`.** -/
theorem not_simplyConnectedSpace_specialOrthogonalGroup (n : ℕ) (hn : 2 ≤ n) :
    ¬ SimplyConnectedSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ) := by
  have h := _root_.CliffordAlgebra.not_simplyConnectedSpace_realSpecialOrthogonal n hn
  rw [realCliffordForm_zero_eq_weightedSumSquares_one] at h
  exact fun _ ↦ h (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivWeightedSumSquaresOne
    (Fin n)).toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end TauCeti
