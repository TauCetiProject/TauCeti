/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Analysis.Matrix.UnitaryGroup.Quaternion
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# Unit Hamilton quaternions, spheres and SU(2)

The unitary Hamilton quaternions are exactly the unit sphere in the four-dimensional real normed
space of quaternions. This gives a canonical homeomorphism between the two subtype presentations.
The algebraic equivalence `Quaternion.unitaryEquivSpecialUnitaryGroup` with the special unitary
group of degree two is an isomorphism of topological groups. Reading off the unique entry of a
`1 × 1` quaternionic unitary matrix extends both identifications to the rank-one compact symplectic
group `Sp(1) = unitary (Matrix ι ι ℍ)` for any singleton index type `ι`.
The group of unit Hamilton quaternions is simply connected. The circle of unit complex quaternions
and the presentation `Sp(1) × U(1) → U(2)`, `(q, w) ↦ w • q`, of the unitary group are continuous.

## Main definitions and results

* `Quaternion.unitaryHomeomorphSphere` identifies the unitary Hamilton quaternions with their unit
  sphere.
* `Quaternion.unitaryHomeomorphEuclideanSphere` identifies them with the unit sphere `S³` of
  `EuclideanSpace ℝ (Fin 4)`.
* `Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup` identifies the unit quaternions with
  the special unitary group of degree two as topological groups.
* `Quaternion.instSimplyConnectedSpaceUnitary`: the unit Hamilton quaternions are simply
  connected.
* `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`: the complex special
  unitary group of degree two is simply connected.
* `Quaternion.continuous_circleToUnitary` and
  `Quaternion.continuous_unitaryProdCircleToUnitaryGroup`: the circle `U(1) → Sp(1)` and the
  surjection `Sp(1) × U(1) → U(2)` are continuous.
* `TauCeti.specialUnitaryGroupTwoHomeomorphSphere`: `SU(2)` is homeomorphic to the unit sphere
  `S³ ⊆ ℍ`.
* `TauCeti.unitaryMatrixQuaternionUniqueHomeomorphSphere`: for a singleton index type `ι`, the
  homeomorphism `unitary (Matrix ι ι ℍ) ≃ₜ sphere (0 : ℍ) 1`.
* `TauCeti.unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup`: for a singleton
  index type `ι`, the topological group isomorphism
  `unitary (Matrix ι ι ℍ) ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ`.

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

/-- **The unit Hamilton quaternions are the unit sphere `S³` of `ℝ⁴`**, through the coordinates
`(re, imI, imJ, imK)` of `Quaternion.linearIsometryEquivTuple`. -/
noncomputable def unitaryHomeomorphEuclideanSphere :
    unitary ℍ[ℝ] ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  unitaryHomeomorphSphere.trans (linearIsometryEquivTuple.toHomeomorph.subtype fun q ↦ by
    simp [-linearIsometryEquivTuple_apply])

/-- The point of `S³` attached to a unit quaternion is its coordinate vector. -/
@[simp]
theorem coe_unitaryHomeomorphEuclideanSphere_apply (q : unitary ℍ[ℝ]) :
    (unitaryHomeomorphEuclideanSphere q : EuclideanSpace ℝ (Fin 4)) =
      linearIsometryEquivTuple (q : ℍ[ℝ]) :=
  (rfl)

/-- The unit quaternion attached to a point of `S³` has that point as coordinate vector. -/
@[simp]
theorem coe_unitaryHomeomorphEuclideanSphere_symm_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    (unitaryHomeomorphEuclideanSphere.symm x : ℍ[ℝ]) = linearIsometryEquivTuple.symm x :=
  (rfl)

/-- Antipodal points of `S³` correspond to opposite unit quaternions. -/
@[simp]
theorem unitaryHomeomorphEuclideanSphere_symm_neg (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    unitaryHomeomorphEuclideanSphere.symm (-x) = -unitaryHomeomorphEuclideanSphere.symm x :=
  Subtype.ext (by simp [Unitary.coe_neg, -linearIsometryEquivTuple_symm_apply])

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

/-- The circle `U(1) → Sp(1)` of unit complex quaternions is continuous. -/
@[fun_prop]
theorem continuous_circleToUnitary : Continuous circleToUnitary :=
  continuous_induced_rng.mpr
    ((ofComplex.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtypeVal).congr
      fun w ↦ by
        simp only [Function.comp_apply, AlgHom.toLinearMap_apply, coe_ofComplex]
        exact (coe_circleToUnitary w).symm)

/-- The surjection `Sp(1) × U(1) → U(2)`, `(q, w) ↦ w • q`, is continuous. -/
@[fun_prop]
theorem continuous_unitaryProdCircleToUnitaryGroup :
    Continuous unitaryProdCircleToUnitaryGroup := by
  refine continuous_induced_rng.mpr ?_
  have h : Continuous fun p : unitary ℍ[ℝ] × Circle ↦
      ((p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ])) :=
    (continuous_subtypeVal.comp continuous_snd).smul
      (toComplexMatrix.toLinearMap.continuous_of_finiteDimensional.comp
        (continuous_subtypeVal.comp continuous_fst))
  exact h.congr fun p ↦ (coe_unitaryProdCircleToUnitaryGroup_apply p).symm

end Quaternion

namespace TauCeti

/-- **`SU(2)` is the three-sphere**: the unit quaternions form the group `SU(2)`, and they are the
unit sphere of `ℍ`. -/
noncomputable def specialUnitaryGroupTwoHomeomorphSphere :
    Matrix.specialUnitaryGroup (Fin 2) ℂ ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

/-- The point of the three-sphere attached to `A ∈ SU(2)` is the unit quaternion whose complex
matrix is `A`. -/
@[simp]
theorem toComplexMatrix_specialUnitaryGroupTwoHomeomorphSphere_apply
    (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Quaternion.toComplexMatrix (specialUnitaryGroupTwoHomeomorphSphere A : ℍ[ℝ]) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- The homeomorphism underlying a continuous multiplicative equivalence applies it, by definition.
  have h : Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph A =
      Quaternion.unitaryEquivSpecialUnitaryGroup.symm A :=
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup_symm_apply A
  rw [specialUnitaryGroupTwoHomeomorphSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply, h]
  exact Quaternion.coe_unitaryEquivSpecialUnitaryGroup_symm_apply A

/-- The element of `SU(2)` attached to a point `q` of the three-sphere is the complex matrix of
the quaternion `q`. -/
@[simp]
theorem coe_specialUnitaryGroupTwoHomeomorphSphere_symm_apply (q : sphere (0 : ℍ[ℝ]) 1) :
    (specialUnitaryGroupTwoHomeomorphSphere.symm q : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (q : ℍ[ℝ]) := by
  rw [← toComplexMatrix_specialUnitaryGroupTwoHomeomorphSphere_apply,
    Homeomorph.apply_symm_apply]

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
