/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Haar integrals on the additive circle as circle averages

For any positive period, normalized Haar measure on `AddCircle T` corresponds to normalized
arc length under `AddCircle.toCircle`. Parametrizing a circle with this map therefore turns its
circle average into a Haar integral. For period `2 * π`, `Complex.arg` also gives the reverse
transport: a Haar integral of `g` equals the circle average of `g ∘ Complex.arg` over the unit
circle. These comparisons let results such as the Poisson integral formula be read as statements
about integrals over the additive circle.
-/

public section

open Complex MeasureTheory Real

namespace AddCircle

/-- Normalized Haar integration on any positive-period additive circle agrees with the
circle average after parametrizing a circle by `AddCircle.toCircle`. -/
theorem integral_haarAddCircle_comp_toCircle {T : ℝ} [Fact (0 < T)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∫ t : AddCircle T, f (R * (toCircle t : ℂ) + c) ∂haarAddCircle) =
      circleAverage f c R := by
  have hT : T ≠ 0 := (Fact.out : 0 < T).ne'
  have hπ : 2 * π ≠ 0 := two_pi_pos.ne'
  rw [integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T 0, zero_add]
  simp only [toCircle_apply_mk, Circle.coe_exp]
  have hparam (t : ℝ) :
      (R : ℂ) * Complex.exp (((2 * π / T * t : ℝ) : ℂ) * I) + c =
        circleMap c R (2 * π / T * t) := by
    simp [circleMap, mul_comm, add_comm]
  simp_rw [hparam]
  rw [intervalIntegral.integral_comp_mul_left (fun t ↦ f (circleMap c R t))
    (div_ne_zero hπ hT)]
  simp only [mul_zero, div_mul_cancel₀ _ hT, smul_smul, circleAverage_def]
  congr 1
  field_simp

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- On the unit circle, `AddCircle.toCircle` inverts `Complex.arg`. -/
theorem toCircle_arg_of_mem_sphere {z : ℂ} (hz : z ∈ Metric.sphere 0 1) :
    (toCircle (Complex.arg z : AddCircle (2 * π)) : ℂ) = z := by
  let u : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
  have hu := Circle.exp_arg u
  simpa [u, toCircle_apply_mk, circleMap] using congrArg Subtype.val hu

/-- A Haar integral over `AddCircle (2 * π)` is the circle average over the unit circle of the
integrand composed with `Complex.arg`. -/
theorem integral_haarAddCircle_eq_circleAverage_arg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : AddCircle (2 * π) → E) :
    ∫ θ, g θ ∂haarAddCircle = circleAverage (fun z ↦ g (Complex.arg z)) 0 1 := by
  rw [integral_haarAddCircle, circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0]
  rw [zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  apply congrArg g
  apply injective_toCircle (mul_ne_zero two_ne_zero pi_ne_zero)
  simpa [toCircle_apply_mk, circleMap] using (Circle.exp_arg (Circle.exp θ)).symm

end AddCircle
