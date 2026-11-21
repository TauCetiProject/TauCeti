/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Compactification.OnePoint.Inversion
import TauCeti.Geometry.Euclidean.Inversion

/-!
# Inversion in the unit circle of the Riemann sphere

The compactified sphere inversion `OnePoint.inversion` in the unit circle of `ℂ` acts on
nonzero finite points by `z ↦ (conj z)⁻¹`. Thus it fixes exactly the unit circle. The closed disc
and its image under inversion meet only along that circle.
-/

public section

open Complex ComplexConjugate

namespace OnePoint

/-- On nonzero finite points, inversion in the unit circle is conjugate reciprocal. -/
theorem inversion_zero_one_coe_eq_conj_inv {z : ℂ} (hz : z ≠ 0) :
    inversion (0 : ℂ) 1 one_ne_zero (z : OnePoint ℂ) = (((conj z)⁻¹ : ℂ) : OnePoint ℂ) := by
  rw [inversion_coe _ _ _ hz, TauCeti.inversion_eq_conj_reciprocal]
  simp

/-- The inversion in the unit circle fixes exactly the points of that circle. -/
theorem inversion_zero_one_eq_self_iff (x : OnePoint ℂ) :
    inversion (0 : ℂ) 1 one_ne_zero x = x ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ (z : OnePoint ℂ) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · rw [inversion_zero_one_coe_eq_conj_inv hz, coe_eq_coe, inv_eq_iff_eq_inv,
        ← mul_eq_one_iff_eq_inv₀ hz, mul_comm, mul_conj']
      norm_cast
      simp [pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero]

/-- Inversion acts as the identity on the unit circle. -/
@[simp] theorem inversion_zero_one_coe_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    inversion (0 : ℂ) 1 one_ne_zero (z : OnePoint ℂ) = z :=
  (inversion_zero_one_eq_self_iff _).2 ⟨z, hz, rfl⟩

/-- The inversion carries a point of the closed unit disc into the closed unit disc only when it
lies on the unit circle, where it is fixed. -/
theorem inversion_zero_one_coe_eq_coe_iff {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    inversion (0 : ℂ) 1 one_ne_zero (w : OnePoint ℂ) = z ↔ ‖w‖ = 1 ∧ z = w := by
  refine ⟨fun h ↦ ?_, fun ⟨hw1, h⟩ ↦ by rw [h, inversion_zero_one_coe_of_norm_eq_one hw1]⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · simp at h
  · rw [inversion_zero_one_coe_eq_conj_inv hw0, coe_eq_coe] at h
    have hnorm : ‖z‖ = ‖w‖⁻¹ := by rw [← h, norm_inv, norm_conj]
    have hw1 : ‖w‖ = 1 :=
      le_antisymm hw ((inv_le_one₀ (norm_pos_iff.2 hw0)).1 (hnorm ▸ hz))
    refine ⟨hw1, ?_⟩
    have := inversion_zero_one_coe_of_norm_eq_one hw1
    rw [inversion_zero_one_coe_eq_conj_inv hw0, coe_eq_coe] at this
    rw [← h, this]

end OnePoint
