/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
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
group of degree two is an isomorphism of topological groups. Reading off the unique entry of a
`1 × 1` quaternionic unitary matrix extends both identifications to the rank-one compact symplectic
group `Sp(1) = unitary (Matrix ι ι ℍ)` for any singleton index type `ι`.
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
* `TauCeti.unitaryMatrixQuaternionUniqueHomeomorphSphere`: for a singleton index type `ι`, the
  homeomorphism `unitary (Matrix ι ι ℍ) ≃ₜ sphere (0 : ℍ) 1`.
* `TauCeti.unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup`: for a singleton
  index type `ι`, the topological group isomorphism
  `unitary (Matrix ι ι ℍ) ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ`.
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
      (toComplexMatrix.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtypeVal)
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

namespace TauCeti

section RankOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

variable (ι) in
/-- **Rank-one symplectic group and the `3`-sphere**: on a singleton index type `ι`, reading off the
unique entry identifies `Sp(1) = unitary (Matrix ι ι ℍ)` homeomorphically with the unit quaternion
sphere `S³ ⊆ ℍ`. -/
noncomputable def unitaryMatrixQuaternionUniqueHomeomorphSphere :
    unitary (Matrix ι ι ℍ) ≃ₜ sphere (0 : ℍ) 1 :=
  (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

@[simp]
theorem coe_unitaryMatrixQuaternionUniqueHomeomorphSphere_apply
    (A : unitary (Matrix ι ι ℍ)) :
    (unitaryMatrixQuaternionUniqueHomeomorphSphere ι A : ℍ) = A.val default default := by
  rw [unitaryMatrixQuaternionUniqueHomeomorphSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply, ContinuousMulEquiv.toHomeomorph_eq_coe]
  exact Matrix.coe_unitaryUniqueContinuousMulEquiv_apply A

@[simp]
theorem coe_unitaryMatrixQuaternionUniqueHomeomorphSphere_symm_apply
    (q : sphere (0 : ℍ) 1) :
    ((unitaryMatrixQuaternionUniqueHomeomorphSphere ι).symm q).val =
      Matrix.of fun _ _ ↦ (q : ℍ) := by
  rw [unitaryMatrixQuaternionUniqueHomeomorphSphere, Homeomorph.symm_trans_apply,
    ContinuousMulEquiv.toHomeomorph_eq_coe, ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact (Matrix.coe_unitaryUniqueContinuousMulEquiv_symm_apply _).trans (by simp)

variable (ι) in
/-- **Rank-one symplectic group and `SU(2)`**: on a singleton index type `ι`, `Sp(1)` is isomorphic
as a topological group to `Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
noncomputable def unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup :
    unitary (Matrix ι ι ℍ) ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).trans
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup

@[simp]
theorem unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup_apply
    (A : unitary (Matrix ι ι ℍ)) :
    unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup ι A =
      Quaternion.unitaryEquivSpecialUnitaryGroup
        (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ A) := by
  simp [unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup]

@[simp]
theorem unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup_symm_apply
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup ι).symm g =
      (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).symm
        (Quaternion.unitaryEquivSpecialUnitaryGroup.symm g) := by
  simp [unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup]

end RankOne

end TauCeti

namespace ContinuousMulEquiv

section QuaternionProd

variable {G : Type*} [TopologicalSpace G]

section Mul

variable [Mul G] (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ])

/-- Transports `G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]` to `G ≃ₜ* SU(2) × SU(2)`. -/
noncomputable def toQuaternionSpecialUnitaryProd :
    G ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  e.trans (Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.prodCongr
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup)

/-- Forward evaluation of `toQuaternionSpecialUnitaryProd`. -/
@[simp]
theorem toQuaternionSpecialUnitaryProd_apply (g : G) :
    e.toQuaternionSpecialUnitaryProd g =
      (Quaternion.unitaryEquivSpecialUnitaryGroup (e g).1,
        Quaternion.unitaryEquivSpecialUnitaryGroup (e g).2) := by
  simp [toQuaternionSpecialUnitaryProd]

/-- Inverse evaluation of `toQuaternionSpecialUnitaryProd`. -/
@[simp]
theorem toQuaternionSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    e.toQuaternionSpecialUnitaryProd.symm M =
      e.symm (Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.1,
        Quaternion.unitaryEquivSpecialUnitaryGroup.symm M.2) := by
  simp [toQuaternionSpecialUnitaryProd]

/-- Transports `G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]` to `G ≃ₜ S³ × S³`. -/
noncomputable def toQuaternionSphereProdHomeomorph :
    G ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  e.toHomeomorph.trans
    (Quaternion.unitaryHomeomorphSphere.prodCongr Quaternion.unitaryHomeomorphSphere)

/-- First quaternion coordinate of `toQuaternionSphereProdHomeomorph`. -/
@[simp]
theorem coe_fst_toQuaternionSphereProdHomeomorph_apply (g : G) :
    ((e.toQuaternionSphereProdHomeomorph g).1 : ℍ[ℝ]) = (e g).1 := by
  simp [toQuaternionSphereProdHomeomorph]; rfl

/-- Second quaternion coordinate of `toQuaternionSphereProdHomeomorph`. -/
@[simp]
theorem coe_snd_toQuaternionSphereProdHomeomorph_apply (g : G) :
    ((e.toQuaternionSphereProdHomeomorph g).2 : ℍ[ℝ]) = (e g).2 := by
  simp [toQuaternionSphereProdHomeomorph]; rfl

/-- Inverse of `toQuaternionSphereProdHomeomorph`. -/
theorem toQuaternionSphereProdHomeomorph_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    e.toQuaternionSphereProdHomeomorph.symm q =
      e.symm (Quaternion.unitaryHomeomorphSphere.symm q.1,
        Quaternion.unitaryHomeomorphSphere.symm q.2) := (rfl)

end Mul

/-- `toQuaternionSphereProdHomeomorph` sends `1` to `(1, 1)`. -/
@[simp]
theorem toQuaternionSphereProdHomeomorph_one [MulOneClass G]
    (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) : e.toQuaternionSphereProdHomeomorph 1 = 1 := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

/-- `toQuaternionSphereProdHomeomorph.symm` sends `(1, 1)` to `1`. -/
@[simp]
theorem toQuaternionSphereProdHomeomorph_symm_one [MulOneClass G]
    (e : G ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]) : e.toQuaternionSphereProdHomeomorph.symm 1 = 1 :=
  e.toQuaternionSphereProdHomeomorph.symm_apply_eq.mpr (toQuaternionSphereProdHomeomorph_one e).symm

end QuaternionProd

end ContinuousMulEquiv
