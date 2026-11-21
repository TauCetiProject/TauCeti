/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius

/-!
# The inversion of the Riemann sphere in the unit circle

The inversion in the unit circle is the homeomorphism `w ↦ (conj w)⁻¹` of the Riemann sphere
`OnePoint ℂ`, exchanging `0` and `∞`. It is complex conjugation followed by the Möbius
transformation `z ↦ 1 / z`. It is an involution whose fixed set is the unit circle.

## Main declarations

* `OnePoint.unitCircleInversion`: the inversion `w ↦ (conj w)⁻¹` of `OnePoint ℂ`.
* `OnePoint.unitCircleInversion_unitCircleInversion`: it is an involution.
* `OnePoint.unitCircleInversion_eq_self_iff`: it fixes exactly the unit circle.
* `OnePoint.unitCircleInversion_coe_eq_coe_iff`: it maps a point of the closed unit disc into the
  closed unit disc only on the unit circle.
-/

public section

open Complex ComplexConjugate Matrix

namespace OnePoint

/-- The inversion of the Riemann sphere in the unit circle, `w ↦ (conj w)⁻¹`, exchanging `0` and
`∞`: complex conjugation followed by the Möbius transformation `z ↦ 1 / z`. -/
noncomputable def unitCircleInversion : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  conjCLE.toHomeomorph.onePointCongr.trans
    (Homeomorph.smul
      (GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (by simp)))

/-- On `ℂ` the inversion is conjugation followed by the inverse of the inverted chart. -/
private theorem unitCircleInversion_coe_eq_invChart_symm (z : ℂ) :
    unitCircleInversion (z : OnePoint ℂ) = invChart.symm (conj z) := by
  simp [unitCircleInversion, invChart_symm_eq_smul]

@[simp]
theorem unitCircleInversion_infty : unitCircleInversion ∞ = ((0 : ℂ) : OnePoint ℂ) := by
  simp [unitCircleInversion, smul_infty_eq_ite, GeneralLinearGroup.mkOfDetNeZero]

@[simp]
theorem unitCircleInversion_zero : unitCircleInversion ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [unitCircleInversion_coe_eq_invChart_symm]

theorem unitCircleInversion_coe {z : ℂ} (hz : z ≠ 0) :
    unitCircleInversion (z : OnePoint ℂ) = (((conj z)⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [unitCircleInversion_coe_eq_invChart_symm, hz]

/-- The inversion in the unit circle is an involution. -/
@[simp]
theorem unitCircleInversion_unitCircleInversion (x : OnePoint ℂ) :
    unitCircleInversion (unitCircleInversion x) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · rw [unitCircleInversion_coe hz, unitCircleInversion_coe (by simpa using hz)]
      simp

@[simp]
theorem unitCircleInversion_symm : unitCircleInversion.symm = unitCircleInversion := by
  ext x
  rw [Homeomorph.symm_apply_eq, unitCircleInversion_unitCircleInversion]

/-- The inversion fixes exactly the unit circle. -/
theorem unitCircleInversion_eq_self_iff (x : OnePoint ℂ) :
    unitCircleInversion x = x ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ (z : OnePoint ℂ) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · rw [unitCircleInversion_coe hz, coe_eq_coe, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv₀ hz,
        mul_comm, mul_conj']
      norm_cast
      simp [pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero]

/-- On the unit circle the inversion is the identity. -/
@[simp]
theorem unitCircleInversion_coe_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    unitCircleInversion (z : OnePoint ℂ) = z :=
  (unitCircleInversion_eq_self_iff _).2 ⟨z, hz, rfl⟩

/-- The inversion carries a point of the closed unit disc into the closed unit disc only when it
lies on the unit circle, where it is fixed. -/
theorem unitCircleInversion_coe_eq_coe_iff {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    unitCircleInversion (w : OnePoint ℂ) = z ↔ ‖w‖ = 1 ∧ z = w := by
  refine ⟨fun h ↦ ?_, fun ⟨hw1, h⟩ ↦ by rw [h, unitCircleInversion_coe_of_norm_eq_one hw1]⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · simp at h
  · rw [unitCircleInversion_coe hw0, coe_eq_coe] at h
    have hnorm : ‖z‖ = ‖w‖⁻¹ := by rw [← h, norm_inv, norm_conj]
    have hw1 : ‖w‖ = 1 :=
      le_antisymm hw ((inv_le_one₀ (norm_pos_iff.2 hw0)).1 (hnorm ▸ hz))
    refine ⟨hw1, ?_⟩
    have := unitCircleInversion_coe_of_norm_eq_one hw1
    rw [unitCircleInversion_coe hw0, coe_eq_coe] at this
    rw [← h, this]

end OnePoint
