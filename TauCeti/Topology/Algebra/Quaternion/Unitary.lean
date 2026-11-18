/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Topology.Algebra.ContinuousMulEquiv

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
* `ContinuousMulEquiv.toQuaternionSpecialUnitaryProd` and
  `ContinuousMulEquiv.toQuaternionSphereProdHomeomorph`: transport any topological group
  isomorphism `G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]` to `SU(2) × SU(2)` and `S³ × S³`.

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

/-- `unitaryHomeomorphSphere` maps `1` to `1`. -/
@[simp]
theorem unitaryHomeomorphSphere_one :
    unitaryHomeomorphSphere 1 = 1 := by
  apply Subtype.ext
  simp

/-- `unitaryHomeomorphSphere.symm` maps `1` to `1`. -/
@[simp]
theorem unitaryHomeomorphSphere_symm_one :
    unitaryHomeomorphSphere.symm 1 = 1 := by
  apply Subtype.ext
  simp

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

namespace ContinuousMulEquiv

/-- Transports a topological group isomorphism `G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]` to
`G ≃ₜ* SU(2) × SU(2)` via `Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup`. -/
noncomputable def toQuaternionSpecialUnitaryProd
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    G ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  e.trans (Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.prodCongr
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup)

/-- Evaluating `toQuaternionSpecialUnitaryProd` applies `Quaternion.unitaryEquivSpecialUnitaryGroup`
to each unit-quaternion factor. -/
@[simp]
theorem toQuaternionSpecialUnitaryProd_apply
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) (g : G) :
    e.toQuaternionSpecialUnitaryProd g =
      (Quaternion.unitaryEquivSpecialUnitaryGroup (e g).1,
        Quaternion.unitaryEquivSpecialUnitaryGroup (e g).2) := by
  simp [toQuaternionSpecialUnitaryProd]

/-- The inverse of `toQuaternionSpecialUnitaryProd` applies
`Quaternion.unitaryEquivSpecialUnitaryGroup.symm` coordinatewise followed by `e.symm`. -/
@[simp]
theorem toQuaternionSpecialUnitaryProd_symm_apply
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ])
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    e.toQuaternionSpecialUnitaryProd.symm M =
      e.symm (Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.1,
        Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.2) := by
  simp [toQuaternionSpecialUnitaryProd]

/-- Transports a topological group isomorphism `G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]` to a
homeomorphism `G ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1` via
`Quaternion.unitaryHomeomorphSphere`. -/
noncomputable def toQuaternionSphereProdHomeomorph
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    G ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  e.toHomeomorph.trans
    (Quaternion.unitaryHomeomorphSphere.prodCongr Quaternion.unitaryHomeomorphSphere)

/-- First quaternion coordinate of `toQuaternionSphereProdHomeomorph`. -/
@[simp]
theorem coe_fst_toQuaternionSphereProdHomeomorph_apply
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) (g : G) :
    ((e.toQuaternionSphereProdHomeomorph g).1 : ℍ[ℝ]) = (e g).1 := by
  rw [toQuaternionSphereProdHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    Prod.map_fst, Quaternion.coe_unitaryHomeomorphSphere_apply]
  rfl

/-- Second quaternion coordinate of `toQuaternionSphereProdHomeomorph`. -/
@[simp]
theorem coe_snd_toQuaternionSphereProdHomeomorph_apply
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) (g : G) :
    ((e.toQuaternionSphereProdHomeomorph g).2 : ℍ[ℝ]) = (e g).2 := by
  rw [toQuaternionSphereProdHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    Prod.map_snd, Quaternion.coe_unitaryHomeomorphSphere_apply]
  rfl

/-- Inverse of `toQuaternionSphereProdHomeomorph`. -/
theorem toQuaternionSphereProdHomeomorph_symm_apply
    {G : Type*} [TopologicalSpace G] [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ])
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    e.toQuaternionSphereProdHomeomorph.symm q =
      e.symm (Quaternion.unitaryHomeomorphSphere.symm q.1,
        Quaternion.unitaryHomeomorphSphere.symm q.2) := by
  rw [toQuaternionSphereProdHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.coe_prodCongr, Prod.map_apply, toHomeomorph_eq_coe, coe_toHomeomorph_symm]
  rfl

/-- `toQuaternionSphereProdHomeomorph` sends `1` to `(1, 1)`. -/
@[simp]
theorem toQuaternionSphereProdHomeomorph_one
    {G : Type*} [TopologicalSpace G] [MulOneClass G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    e.toQuaternionSphereProdHomeomorph 1 = 1 := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

/-- `toQuaternionSphereProdHomeomorph.symm` sends `(1, 1)` to `1`. -/
@[simp]
theorem toQuaternionSphereProdHomeomorph_symm_one
    {G : Type*} [TopologicalSpace G] [MulOneClass G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    e.toQuaternionSphereProdHomeomorph.symm 1 = 1 :=
  e.toQuaternionSphereProdHomeomorph.symm_apply_eq.mpr
    (toQuaternionSphereProdHomeomorph_one e).symm

end ContinuousMulEquiv
