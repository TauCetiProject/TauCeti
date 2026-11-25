/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Complex.Pick.Herglotz.Basic

/-!
# Examples: the Herglotz representation in resolvent convention

The Nevanlinna measure `ρ` and the Herglotz measure `ν` of a Pick function are related by the
density change `dν = (1 + t ^ 2) dρ`, and the weighted mass `∫ (1 + t ^ 2)⁻¹ dν` is `ρ(ℝ)`.

* For `ρ = 0` also `ν = 0`, and the representation reduces to `a + b z`.
* For `ρ = δ₂` the measure is `ν = 5 δ₂`, of weighted mass `1`. The reciprocal density
  `(1 + t ^ 2)⁻¹` would give `δ₂ / 5`, of weighted mass `1 / 25`.
* For `F z = z` the unique triple is `(a, b, ν) = (0, 1, 0)`. The reversed sign `F z = -z` has
  negative imaginary part at `i`, so it is not a Pick function.
-/

open Complex MeasureTheory TauCeti

-- For `ρ = 0` the density change gives `ν = 0`.
example : (0 : Measure ℝ).withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) = 0 :=
  withDensity_zero_left _

-- For `ν = 0` the representation reduces to `a + b z`.
example (a b : ℝ) (z : ℂ) :
    (a : ℂ) + b * z + ∫ t, subtractedResolventKernel z t ∂(0 : Measure ℝ) = a + b * z := by
  simp

-- For `ρ = δ₂` the density change gives `ν = 5 δ₂`.
example : (Measure.dirac (2 : ℝ)).withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) =
    (5 : ENNReal) • Measure.dirac 2 := by
  rw [dirac_withDensity]
  norm_num

-- Its weighted mass is `δ₂(ℝ) = 1`.
example : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹
    ∂(Measure.dirac (2 : ℝ)).withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) = 1 := by
  rw [Measure.lintegral_inv_one_add_sq_withDensity, measure_univ]

-- Using the reciprocal density instead gives the wrong weighted mass `1 / 25`.
example : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹
    ∂(Measure.dirac (2 : ℝ)).withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹) =
      ENNReal.ofReal (1 / 25) := by
  norm_num [dirac_withDensity, ← ENNReal.ofReal_mul]

-- `F z = z` is represented by the triple `(0, 1, 0)`, and this triple is the only one.
example (p : ℝ × ℝ × Measure ℝ) :
    (0 ≤ p.2.1 ∧ ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂p.2.2 < ⊤ ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        z = p.1 + p.2.1 * z + ∫ t, subtractedResolventKernel z t ∂p.2.2) ↔ p = (0, 1, 0) := by
  have hp := existsUnique_eq_subtractedResolventKernel_add (F := fun z ↦ z)
    differentiableOn_id fun z hz ↦ le_of_lt hz
  have h0 : 0 ≤ (1 : ℝ) ∧ ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂(0 : Measure ℝ) < ⊤ ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        z = (0 : ℝ) + (1 : ℝ) * z + ∫ t, subtractedResolventKernel z t ∂(0 : Measure ℝ) :=
    ⟨zero_le_one, by simp, fun z _ ↦ by simp⟩
  exact ⟨fun h ↦ hp.unique h h0, fun h ↦ h ▸ h0⟩

-- Reversing the sign, `F z = -z`, gives a function with negative imaginary part at `i`.
example : ¬ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (-z).im :=
  fun h ↦ absurd (h I (by simp)) (by simp)
