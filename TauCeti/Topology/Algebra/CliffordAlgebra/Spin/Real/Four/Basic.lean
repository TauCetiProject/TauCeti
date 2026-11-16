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
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four` — the native reduction
`TauCeti.realSpinFourEquivQuaternionUnitaryProd` and the calibrated `(1, i, j, k)` model
`TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd` — factor through reversal-preserving
algebra equivalences on the finite-dimensional even Clifford algebra `Cl⁺(4,0)`. By
`CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd`, both equivalences upgrade to
topological group isomorphisms with `unitary ℍ[ℝ] × unitary ℍ[ℝ]`, and via
`ContinuousMulEquiv.toQuaternionSpecialUnitaryProd` and
`ContinuousMulEquiv.toQuaternionSphereProdHomeomorph` yield topological group isomorphisms with
`SU(2) × SU(2)` and homeomorphisms with the sphere product `S³ × S³ ⊆ ℍ × ℍ`.

## Main definitions

* `TauCeti.realSpinFourContinuousMulEquivQuaternionUnitaryProd`,
  `TauCeti.realSpinFourContinuousMulEquivSpecialUnitaryProd`, and
  `TauCeti.realSpinFourHomeomorphQuaternionSphereProd`: native topological group and
  `S³ × S³` homeomorphism models of compact `Spin(4)`.
* `TauCeti.realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd`,
  `TauCeti.realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd`, and
  `TauCeti.realSpinFourCalibratedHomeomorphQuaternionSphereProd`: calibrated `(1, i, j, k)`
  topological group and `S³ × S³` homeomorphism models of compact `Spin(4)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open Metric
open scoped Quaternion

namespace TauCeti

/-! ### Native `Spin(4)` topological models -/

/-- **Native topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`.** -/
noncomputable def realSpinFourContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroEvenEquivQuaternionProd
    realCliffordFourZeroEvenEquivQuaternionProd_reverseEven

/-- `realSpinFourContinuousMulEquivQuaternionUnitaryProd` has
`realSpinFourEquivQuaternionUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourEquivQuaternionUnitaryProd s := by
  rw [realSpinFourContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
    ← realSpinFourEquivQuaternionUnitaryProd_eq]

/-- The inverse of `realSpinFourContinuousMulEquivQuaternionUnitaryProd` is
`realSpinFourEquivQuaternionUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourEquivQuaternionUnitaryProd.symm q := by
  rw [realSpinFourContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply,
    ← realSpinFourEquivQuaternionUnitaryProd_eq]

/-- The native algebraic equivalence from compact `Spin(4)` to pairs of unit Hamilton quaternions
is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourEquivQuaternionUnitaryProd :
    Continuous (realSpinFourEquivQuaternionUnitaryProd :
      spinGroup (realCliffordForm 4 0) → unitary ℍ[ℝ] × unitary ℍ[ℝ]) :=
  (map_continuous realSpinFourContinuousMulEquivQuaternionUnitaryProd).congr
    realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply

/-- **Native topological group isomorphism `Spin(4) ≃ₜ* SU(2) × SU(2)`.** -/
noncomputable def realSpinFourContinuousMulEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourContinuousMulEquivQuaternionUnitaryProd.toQuaternionSpecialUnitaryProd

/-- `realSpinFourContinuousMulEquivSpecialUnitaryProd` has `realSpinFourEquivSpecialUnitaryProd`
as its forward map. -/
@[simp]
theorem realSpinFourContinuousMulEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourContinuousMulEquivSpecialUnitaryProd s = realSpinFourEquivSpecialUnitaryProd s := by
  rw [realSpinFourContinuousMulEquivSpecialUnitaryProd,
    ContinuousMulEquiv.toQuaternionSpecialUnitaryProd_apply,
    realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply,
    realSpinFourEquivSpecialUnitaryProd_eq]
  rfl

/-- The inverse of `realSpinFourContinuousMulEquivSpecialUnitaryProd` is
`realSpinFourEquivSpecialUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourContinuousMulEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourContinuousMulEquivSpecialUnitaryProd.symm M =
      realSpinFourEquivSpecialUnitaryProd.symm M := by
  rw [realSpinFourContinuousMulEquivSpecialUnitaryProd,
    ContinuousMulEquiv.toQuaternionSpecialUnitaryProd_symm_apply,
    realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply,
    realSpinFourEquivSpecialUnitaryProd_eq]
  rfl

/-- The native algebraic equivalence `Spin(4) ≃* SU(2) × SU(2)` is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourEquivSpecialUnitaryProd :
    Continuous (realSpinFourEquivSpecialUnitaryProd :
      spinGroup (realCliffordForm 4 0) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  (map_continuous realSpinFourContinuousMulEquivSpecialUnitaryProd).congr
    realSpinFourContinuousMulEquivSpecialUnitaryProd_apply

/-- Native homeomorphism from compact `Spin(4)` to the product of two unit quaternion spheres. -/
noncomputable def realSpinFourHomeomorphQuaternionSphereProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  realSpinFourContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph

/-- First quaternion coordinate of `realSpinFourHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_fst_realSpinFourHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourHomeomorphQuaternionSphereProd s).1 : ℍ[ℝ]) =
      (realSpinFourEquivQuaternionUnitaryProd s).1 := by
  simp [realSpinFourHomeomorphQuaternionSphereProd]

/-- Second quaternion coordinate of `realSpinFourHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_snd_realSpinFourHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourHomeomorphQuaternionSphereProd s).2 : ℍ[ℝ]) =
      (realSpinFourEquivQuaternionUnitaryProd s).2 := by
  simp [realSpinFourHomeomorphQuaternionSphereProd]

/-- Inverse of `realSpinFourHomeomorphQuaternionSphereProd`. -/
theorem realSpinFourHomeomorphQuaternionSphereProd_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    realSpinFourHomeomorphQuaternionSphereProd.symm q =
      realSpinFourEquivQuaternionUnitaryProd.symm
        (Quaternion.unitaryHomeomorphSphere.symm q.1,
          Quaternion.unitaryHomeomorphSphere.symm q.2) := by
  simp [realSpinFourHomeomorphQuaternionSphereProd,
    ContinuousMulEquiv.toQuaternionSphereProdHomeomorph_symm_apply]

/-- `realSpinFourHomeomorphQuaternionSphereProd` sends `1` to `(1, 1)`. -/
@[simp]
theorem realSpinFourHomeomorphQuaternionSphereProd_one :
    realSpinFourHomeomorphQuaternionSphereProd 1 = 1 :=
  realSpinFourContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph_one

/-- `realSpinFourHomeomorphQuaternionSphereProd.symm` sends `(1, 1)` to `1`. -/
@[simp]
theorem realSpinFourHomeomorphQuaternionSphereProd_symm_one :
    realSpinFourHomeomorphQuaternionSphereProd.symm 1 = 1 :=
  realSpinFourContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph_symm_one

/-! ### Calibrated `(1, i, j, k)` `Spin(4)` topological models -/

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`**, aligned
with the standard `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd
    (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0) (by simp)
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realCliffordFourZeroCalibratedEvenEquivQuaternionProd_reverseEven

/-- `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd` has
`realSpinFourCalibratedEquivQuaternionUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourCalibratedEquivQuaternionUnitaryProd s := by
  rw [realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
    ← realSpinFourCalibratedEquivQuaternionUnitaryProd_eq]

/-- The inverse of `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd` is
`realSpinFourCalibratedEquivQuaternionUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q := by
  rw [realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd,
    CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply,
    ← realSpinFourCalibratedEquivQuaternionUnitaryProd_eq]

/-- The calibrated `(1, i, j, k)` equivalence from compact `Spin(4)` to pairs of unit Hamilton
quaternions is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd :
    Continuous (realSpinFourCalibratedEquivQuaternionUnitaryProd :
      spinGroup (realCliffordForm 4 0) → unitary ℍ[ℝ] × unitary ℍ[ℝ]) :=
  (map_continuous realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd).congr
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* SU(2) × SU(2)`**, aligned with the
standard `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toQuaternionSpecialUnitaryProd

/-- `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd` has
`realSpinFourCalibratedEquivSpecialUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd s =
      realSpinFourCalibratedEquivSpecialUnitaryProd s := by
  simp [realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd]

/-- The inverse of `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd` is
`realSpinFourCalibratedEquivSpecialUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd.symm M =
      realSpinFourCalibratedEquivSpecialUnitaryProd.symm M := by
  simp [realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd]

/-- The calibrated algebraic equivalence `Spin(4) ≃* SU(2) × SU(2)` is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourCalibratedEquivSpecialUnitaryProd :
    Continuous (realSpinFourCalibratedEquivSpecialUnitaryProd :
      spinGroup (realCliffordForm 4 0) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  (map_continuous realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd).congr
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_apply

/-- **Calibrated homeomorphism `Spin(4) ≃ₜ S³ × S³`** in the standard `(1, i, j, k)` quaternion
coordinates. -/
noncomputable def realSpinFourCalibratedHomeomorphQuaternionSphereProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toQuaternionSphereProdHomeomorph

/-- First quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_fst_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourCalibratedHomeomorphQuaternionSphereProd s).1 : ℍ[ℝ]) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 := by
  simp [realSpinFourCalibratedHomeomorphQuaternionSphereProd]

/-- Second quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_snd_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
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
@[simp]
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd 1 = 1 :=
  ContinuousMulEquiv.toQuaternionSphereProdHomeomorph_one
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd

/-- `realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm` sends `(1, 1)` to `1`. -/
@[simp]
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm 1 = 1 :=
  ContinuousMulEquiv.toQuaternionSphereProdHomeomorph_symm_one
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd

end TauCeti
end
