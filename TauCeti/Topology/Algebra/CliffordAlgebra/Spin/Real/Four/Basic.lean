/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.Quaternion.Unitary
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Four

/-!
# Topological group and sphere-product models of compact `Spin(4)`

Both quaternion-pair models of compact `Spin(4)` from
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four` upgrade via
`CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd` to topological group isomorphisms
with `unitary ℍ[ℝ] × unitary ℍ[ℝ]`, and the calibrated `(1, i, j, k)` model further upgrades via
`ContinuousMulEquiv.toQuaternionSpecialUnitaryProd` and
`ContinuousMulEquiv.toQuaternionSphereProdHomeomorph` to `SU(2) × SU(2)` and `S³ × S³ ⊆ ℍ × ℍ`.

## Main definitions and results

* `TauCeti.realSpinFourContinuousMulEquivQuaternionUnitaryProd` (with `@[fun_prop]` continuity of
  `realSpinFourEquivQuaternionUnitaryProd` and its inverse): native topological group model of
  `Spin(4)`.
* `TauCeti.realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd` (with `@[fun_prop]`
  continuity of `realSpinFourCalibratedEquivQuaternionUnitaryProd` and its inverse),
  `TauCeti.realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd`, and
  `TauCeti.realSpinFourCalibratedHomeomorphQuaternionSphereProd`: calibrated `(1, i, j, k)` models.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open Metric
open scoped Quaternion

namespace TauCeti

section Spin4

variable (s : spinGroup (realCliffordForm 4 0))

/-! ### Native `Spin(4)` topological model -/

/-- **Native topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`.** -/
noncomputable def realSpinFourContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp) realCliffordFourZeroEvenEquivQuaternionProd
    realCliffordFourZeroEvenEquivQuaternionProd_reverseEven

/-- Forward evaluation of `realSpinFourContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp] theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourEquivQuaternionUnitaryProd s := by
  rw [realSpinFourContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
    ← realSpinFourEquivQuaternionUnitaryProd_eq]

/-- Inverse of `realSpinFourContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp] theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourEquivQuaternionUnitaryProd.symm q := by
  rw [realSpinFourContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply,
    ← realSpinFourEquivQuaternionUnitaryProd_eq]

/-- Continuity of `realSpinFourEquivQuaternionUnitaryProd`. -/
@[fun_prop] theorem continuous_realSpinFourEquivQuaternionUnitaryProd :
    Continuous ⇑realSpinFourEquivQuaternionUnitaryProd :=
  (map_continuous realSpinFourContinuousMulEquivQuaternionUnitaryProd).congr
    realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply

/-- The inverse of the compact `Spin(4)` equivalence with pairs of unit quaternions is
continuous. -/
@[fun_prop] theorem continuous_realSpinFourEquivQuaternionUnitaryProd_symm :
    Continuous realSpinFourEquivQuaternionUnitaryProd.symm :=
  (map_continuous realSpinFourContinuousMulEquivQuaternionUnitaryProd.symm).congr
    realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply

/-! ### Calibrated `(1, i, j, k)` `Spin(4)` topological models -/

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`.** -/
noncomputable def realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd (realCliffordForm 4 0)
    (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven

/-- Forward evaluation of `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourCalibratedEquivQuaternionUnitaryProd s := by
  rw [realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
    ← realSpinFourCalibratedEquivQuaternionUnitaryProd_def]

/-- Inverse of `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q := by
  rw [realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply,
    ← realSpinFourCalibratedEquivQuaternionUnitaryProd_def]

/-- Continuity of `realSpinFourCalibratedEquivQuaternionUnitaryProd`. -/
@[fun_prop] theorem continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd :
    Continuous ⇑realSpinFourCalibratedEquivQuaternionUnitaryProd :=
  (map_continuous realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd).congr
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply

/-- The inverse of the calibrated compact `Spin(4)` equivalence with pairs of unit quaternions is
continuous. -/
@[fun_prop] theorem continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd_symm :
    Continuous realSpinFourCalibratedEquivQuaternionUnitaryProd.symm :=
  (map_continuous realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.symm).congr
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_symm_apply

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* SU(2) × SU(2)`.** -/
noncomputable def realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toQuaternionSpecialUnitaryProd

/-- Forward evaluation of `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_apply :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd s =
      realSpinFourCalibratedEquivSpecialUnitaryProd s := by
  simp [realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd]

/-- Inverse of `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd`. -/
@[simp] theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd.symm M =
      realSpinFourCalibratedEquivSpecialUnitaryProd.symm M := by
  simp [realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd]

/-- Continuity of `realSpinFourCalibratedEquivSpecialUnitaryProd`. -/
@[fun_prop] theorem continuous_realSpinFourCalibratedEquivSpecialUnitaryProd :
    Continuous ⇑realSpinFourCalibratedEquivSpecialUnitaryProd :=
  (map_continuous realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd).congr
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_apply

/-- **Calibrated homeomorphism `Spin(4) ≃ₜ S³ × S³`** in `(1, i, j, k)` coordinates. -/
noncomputable def realSpinFourCalibratedHomeomorphQuaternionSphereProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph

/-- First quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp] theorem coe_fst_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply :
    ((realSpinFourCalibratedHomeomorphQuaternionSphereProd s).1 : ℍ[ℝ]) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 := by
  simp [realSpinFourCalibratedHomeomorphQuaternionSphereProd]

/-- Second quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp] theorem coe_snd_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply :
    ((realSpinFourCalibratedHomeomorphQuaternionSphereProd s).2 : ℍ[ℝ]) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  simp [realSpinFourCalibratedHomeomorphQuaternionSphereProd]

/-- Inverse of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm q =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm
        (Quaternion.unitaryHomeomorphSphere.symm q.1,
          Quaternion.unitaryHomeomorphSphere.symm q.2) := by
  simp [realSpinFourCalibratedHomeomorphQuaternionSphereProd,
    ContinuousMulEquiv.toQuaternionSphereProdHomeomorph_symm_apply]

/-- `realSpinFourCalibratedHomeomorphQuaternionSphereProd` sends `1` to `(1, 1)`. -/
@[simp] theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd 1 = 1 :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph_one

/-- `realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm` sends `(1, 1)` to `1`. -/
@[simp] theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm 1 = 1 :=
  ContinuousMulEquiv.toQuaternionSphereProdHomeomorph_symm_one
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd

end Spin4

end TauCeti
end
