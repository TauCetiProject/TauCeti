/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# Unit Hamilton quaternions, spheres and SU(2)

The unitary Hamilton quaternions are exactly the unit sphere in the four-dimensional real normed
space of quaternions. This gives a canonical homeomorphism between the two subtype presentations.
The algebraic equivalence `Quaternion.unitaryEquivSpecialUnitaryGroup` with the special unitary
group of degree two is an isomorphism of topological groups.
The group of unit Hamilton quaternions is simply connected.

## Main definitions and results

* `Quaternion.unitaryHomeomorphSphere` identifies the unitary Hamilton quaternions with their unit
  sphere.
* `Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup` identifies the unit quaternions with
  the special unitary group of degree two as topological groups.
* `Quaternion.instSimplyConnectedSpaceUnitary`: the unit Hamilton quaternions are simply
  connected.
* `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`: the complex special
  unitary group of degree two is simply connected.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Example 2.5(5) and Exercise 2.11.
-/

public section

open Metric
open scoped Quaternion

namespace Quaternion

/-- A Hamilton quaternion is unitary exactly when it belongs to the unit sphere. -/
@[simp 1100]
theorem mem_unitary_iff_mem_sphere_zero_one (q : ℍ[ℝ]) :
    q ∈ unitary ℍ[ℝ] ↔ q ∈ sphere (0 : ℍ[ℝ]) 1 := by
  rw [mem_unitary_iff_normSq_eq_one, mem_sphere, dist_zero_right,
    normSq_eq_norm_mul_self]
  constructor
  · intro h
    nlinarith [norm_nonneg q]
  · intro h
    rw [h]
    norm_num

/-- The unitary Hamilton quaternions are homeomorphic to the unit sphere in `ℍ`. -/
noncomputable def unitaryHomeomorphSphere :
    unitary ℍ[ℝ] ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  Homeomorph.ofEqSubtypes (by
    funext q
    exact propext (mem_unitary_iff_mem_sphere_zero_one q))

/-- The homeomorphism from unitary quaternions to the unit sphere preserves the underlying
quaternion. -/
@[simp]
theorem coe_unitaryHomeomorphSphere_apply (q : unitary ℍ[ℝ]) :
    (unitaryHomeomorphSphere q : ℍ[ℝ]) = q := by
  rw [unitaryHomeomorphSphere]
  rfl

/-- The inverse homeomorphism from the unit sphere preserves the underlying quaternion. -/
@[simp]
theorem coe_unitaryHomeomorphSphere_symm_apply (q : sphere (0 : ℍ[ℝ]) 1) :
    (unitaryHomeomorphSphere.symm q : ℍ[ℝ]) = q := by
  rw [unitaryHomeomorphSphere]
  rfl

/-- The group of unit Hamilton quaternions is simply connected. -/
instance instSimplyConnectedSpaceUnitary : SimplyConnectedSpace (unitary ℍ[ℝ]) := by
  let _ : SimplyConnectedSpace (sphere (0 : ℍ[ℝ]) 1) := by
    apply TauCeti.simplyConnectedSpace_sphere
    · rw [Quaternion.rank_eq_four]
      norm_num
    · positivity
  exact unitaryHomeomorphSphere.toHomotopyEquiv.simplyConnectedSpace

/-- The unit Hamilton quaternions and the special unitary group of degree two are isomorphic
as topological groups. -/
noncomputable def unitaryContinuousMulEquivSpecialUnitaryGroup :
    unitary ℍ[ℝ] ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  let _ : CompactSpace (unitary ℍ[ℝ]) := unitaryHomeomorphSphere.symm.compactSpace
  have hf : Continuous unitaryEquivSpecialUnitaryGroup := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, coe_unitaryEquivSpecialUnitaryGroup_apply,
      AlgHom.coe_toLinearMap, StarAlgHom.coe_toAlgHom] using
      (toComplexMatrix.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val)
  exact { __ := unitaryEquivSpecialUnitaryGroup
          __ := unitaryEquivSpecialUnitaryGroup.toEquiv.toHomeomorphOfContinuousClosed
            hf hf.isClosedMap }

/-- The topological group equivalence has the forward map of the algebraic equivalence. -/
@[simp]
theorem unitaryContinuousMulEquivSpecialUnitaryGroup_apply (q : unitary ℍ[ℝ]) :
    unitaryContinuousMulEquivSpecialUnitaryGroup q = unitaryEquivSpecialUnitaryGroup q := by
  rw [unitaryContinuousMulEquivSpecialUnitaryGroup]
  rfl

/-- The inverse topological group equivalence has the inverse map of the algebraic equivalence. -/
@[simp]
theorem unitaryContinuousMulEquivSpecialUnitaryGroup_symm_apply
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    unitaryContinuousMulEquivSpecialUnitaryGroup.symm g =
      unitaryEquivSpecialUnitaryGroup.symm g := by
  rw [unitaryContinuousMulEquivSpecialUnitaryGroup]
  rfl

/-- The complex special unitary group of degree two is simply connected. -/
instance _root_.Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex :
    SimplyConnectedSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  let e := unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph
  exact e.toHomotopyEquiv.simplyConnectedSpace

end Quaternion
