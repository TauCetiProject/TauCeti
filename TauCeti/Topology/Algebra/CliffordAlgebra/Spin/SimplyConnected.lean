/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
public import TauCeti.Topology.Algebra.Quaternion.Unitary

/-!
# Simple-connectedness of the compact three-dimensional Spin group

The algebraic equivalence from compact `Spin(3)` to the unit Hamilton quaternions is continuous.
Compactness of the source upgrades it to a continuous multiplicative equivalence. Unit quaternions
form the unit sphere in the four-dimensional real space `ℍ`, so the existing simple-connectedness
theorem for spheres proves that compact `Spin(3)` is simply connected.

## Main results

* `TauCeti.realSpinThreeContinuousMulEquivQuaternionUnitary` upgrades the quaternion model of
  compact `Spin(3)` to an equivalence of topological groups.
* `TauCeti.realSpinThreeHomeomorphQuaternionSphere` identifies compact `Spin(3)` with the unit
  quaternion sphere.
* `CliffordAlgebra.simplyConnectedSpace_realCliffordSpinGroupZero_three` proves that compact
  `Spin(3)` is simply connected.

## Reference

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §6.
-/

public section

open Metric
open scoped Quaternion

namespace TauCeti

/-- The algebraic equivalence from compact `Spin(3)` to the unit Hamilton quaternions is
continuous. -/
theorem continuous_realSpinThreeEquivQuaternionUnitary :
    Continuous (realSpinThreeEquivQuaternionUnitary :
      spinGroup (realCliffordForm 3 0) → unitary ℍ[ℝ]) := by
  apply continuous_induced_rng.2
  have hfun : Subtype.val ∘ (realSpinThreeEquivQuaternionUnitary :
      spinGroup (realCliffordForm 3 0) → unitary ℍ[ℝ]) =
      fun s ↦ realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) := by
    funext s
    exact coe_realSpinThreeEquivQuaternionUnitary_apply s
  rw [hfun]
  let _ : IsTopologicalAddGroup (CliffordAlgebra.even (realCliffordForm 3 0)) :=
    (CliffordAlgebra.even (realCliffordForm 3 0)).toSubmodule.isTopologicalAddGroup
  have hinner : Continuous (fun s ↦
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
        (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) := by
    apply continuous_induced_rng.2
    have hinnerFun : Subtype.val ∘ (fun s ↦
        CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) =
        fun s : spinGroup (realCliffordForm 3 0) ↦
          (s : CliffordAlgebra (realCliffordForm 3 0)) := by
      funext s
      simp only [Function.comp_apply, CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
        CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
      rfl
    rw [hinnerFun]
    exact continuous_subtype_val
  exact realCliffordThreeZeroEvenEquivQuaternion.toLinearMap.continuous_of_finiteDimensional.comp
    hinner

/-- Compact `Spin(3)` is continuously multiplicatively equivalent to the unit Hamilton
quaternions. -/
noncomputable def realSpinThreeContinuousMulEquivQuaternionUnitary :
    spinGroup (realCliffordForm 3 0) ≃ₜ* unitary ℍ[ℝ] :=
  ContinuousMulEquiv.mk realSpinThreeEquivQuaternionUnitary
    continuous_realSpinThreeEquivQuaternionUnitary
    (continuous_realSpinThreeEquivQuaternionUnitary.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinThreeEquivQuaternionUnitary.toEquiv))

/-- The topological quaternion equivalence has the existing algebraic equivalence as its forward
map. -/
@[simp]
theorem realSpinThreeContinuousMulEquivQuaternionUnitary_apply
    (s : spinGroup (realCliffordForm 3 0)) :
    realSpinThreeContinuousMulEquivQuaternionUnitary s =
      realSpinThreeEquivQuaternionUnitary s := by
  rw [realSpinThreeContinuousMulEquivQuaternionUnitary]
  rfl

/-- The inverse topological quaternion equivalence has the existing algebraic inverse as its
map. -/
@[simp]
theorem realSpinThreeContinuousMulEquivQuaternionUnitary_symm_apply
    (q : unitary ℍ[ℝ]) :
    realSpinThreeContinuousMulEquivQuaternionUnitary.symm q =
      realSpinThreeEquivQuaternionUnitary.symm q := by
  rw [realSpinThreeContinuousMulEquivQuaternionUnitary]
  rfl

/-- Compact `Spin(3)` is homeomorphic to the unit sphere in the real quaternion space. -/
noncomputable def realSpinThreeHomeomorphQuaternionSphere :
    spinGroup (realCliffordForm 3 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  realSpinThreeContinuousMulEquivQuaternionUnitary.toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

/-- The homeomorphism from compact `Spin(3)` to the quaternion sphere applies the existing
quaternion equivalence to the underlying element. -/
@[simp]
theorem coe_realSpinThreeHomeomorphQuaternionSphere_apply
    (s : spinGroup (realCliffordForm 3 0)) :
    (realSpinThreeHomeomorphQuaternionSphere s : ℍ[ℝ]) =
      realSpinThreeEquivQuaternionUnitary s := by
  rw [realSpinThreeHomeomorphQuaternionSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg Subtype.val (realSpinThreeContinuousMulEquivQuaternionUnitary_apply s)

/-- The inverse sphere homeomorphism is the inverse of the existing algebraic equivalence after
viewing a sphere point as a unitary quaternion. -/
@[simp]
theorem realSpinThreeHomeomorphQuaternionSphere_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1) :
    realSpinThreeHomeomorphQuaternionSphere.symm q =
      realSpinThreeEquivQuaternionUnitary.symm
        (Quaternion.unitaryHomeomorphSphere.symm q) := by
  rw [realSpinThreeHomeomorphQuaternionSphere, Homeomorph.symm_trans_apply]
  rw [ContinuousMulEquiv.toHomeomorph_eq_coe,
    ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact realSpinThreeContinuousMulEquivQuaternionUnitary_symm_apply
    (Quaternion.unitaryHomeomorphSphere.symm q)

end TauCeti

namespace CliffordAlgebra

open TauCeti

/-- The compact three-dimensional real Spin group is simply connected. -/
theorem simplyConnectedSpace_realCliffordSpinGroupZero_three :
    SimplyConnectedSpace (realCliffordSpinGroupZero 3) := by
  let _ : SimplyConnectedSpace (sphere (0 : ℍ[ℝ]) 1) := by
    apply simplyConnectedSpace_sphere
    · rw [Quaternion.rank_eq_four]
      norm_num
    · positivity
  exact realSpinThreeHomeomorphQuaternionSphere.toHomotopyEquiv.simplyConnectedSpace

end CliffordAlgebra
