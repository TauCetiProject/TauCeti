/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivative of the integral of `exp (u + t v)`

For functions `u` and `v` such that `exp (u + s v)` is integrable for every real `s` near `t₀`,
this file differentiates `t ↦ ∫ exp (u + t v) dμ` under the integral sign:

`d/dt ∫ exp (u + t v) dμ = ∫ v exp (u + t v) dμ`.

This is the directional derivative of the exponential integral `∫ e^u dμ` at `u` in the direction
`v`, the derivative of the exponential term in Liouville-type energies such as
`TauCeti.Manifold.liouvilleEnergy`. The integrability hypothesis holds for continuous `u` and `v`
on a compact space with a finite measure, and, by Trudinger's inequality, for the values of
`H¹` functions on a closed surface.

## Main declarations

* `TauCeti.hasDerivAt_integral_exp_add_mul`: the derivative of `t ↦ ∫ exp (u + t v) dμ`.
-/

public section

open MeasureTheory

open scoped Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Differentiating `∫ exp (u + t v) dμ`.** Let `exp (u + s v)` be integrable for every real `s`
near `t₀`. Then the derivative of `t ↦ ∫ exp (u + t v) dμ` at `t₀` is `∫ v exp (u + t₀ v) dμ`. -/
theorem hasDerivAt_integral_exp_add_mul {u v : X → ℝ} {t₀ : ℝ}
    (hint : ∀ᶠ s in 𝓝 t₀, Integrable (fun x ↦ Real.exp (u x + s * v x)) μ) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, Real.exp (u x + t * v x) ∂μ)
      (∫ x, v x * Real.exp (u x + t₀ * v x) ∂μ) t₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hint
  set δ := ε / 3 with hδ
  have hδ0 : 0 < δ := by positivity
  have hint₀ := hball t₀ (Metric.mem_ball_self hε)
  have hint_add := hball (t₀ + 2 * δ) (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hint_sub := hball (t₀ - 2 * δ) (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  -- `v` is measurable, as the difference quotient of the exponents at `t₀ + 2δ` and `t₀`.
  have hv : AEStronglyMeasurable v μ := by
    have h := ((Real.aemeasurable_of_aemeasurable_exp hint_add.aemeasurable).sub
      (Real.aemeasurable_of_aemeasurable_exp hint₀.aemeasurable)).const_mul (2 * δ)⁻¹
    refine (h.congr (ae_of_all _ fun x ↦ ?_)).aestronglyMeasurable
    simp only [Pi.sub_apply]
    field_simp
    ring
  -- On `|t - t₀| < δ`, the bound `|v| ≤ δ⁻¹ exp (δ |v|)` gives
  -- `|v e^(u + t v)| ≤ δ⁻¹ e^(u + t₀ v + 2 δ |v|)`,
  -- which is at most `δ⁻¹ (e^(u + (t₀ + 2δ) v) + e^(u + (t₀ - 2δ) v))`.
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball t₀ δ) :
      ‖v x * Real.exp (u x + t * v x)‖ ≤
        δ⁻¹ * (Real.exp (u x + (t₀ + 2 * δ) * v x) + Real.exp (u x + (t₀ - 2 * δ) * v x)) := by
    have ht' : |t - t₀| ≤ δ := (Real.dist_eq t t₀ ▸ Metric.mem_ball.1 ht).le
    have hv1 : |v x| ≤ δ⁻¹ * Real.exp (δ * |v x|) := by
      rw [le_inv_mul_iff₀ hδ0]
      linarith [Real.add_one_le_exp (δ * |v x|)]
    have htv : t * v x ≤ t₀ * v x + δ * |v x| := by
      have : (t - t₀) * v x ≤ δ * |v x| := by
        calc (t - t₀) * v x ≤ |(t - t₀) * v x| := le_abs_self _
          _ = |t - t₀| * |v x| := abs_mul _ _
          _ ≤ δ * |v x| := by gcongr
      linarith
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc |v x| * Real.exp (u x + t * v x)
        ≤ δ⁻¹ * Real.exp (δ * |v x|) * Real.exp (u x + t * v x) := by gcongr
      _ = δ⁻¹ * Real.exp (u x + t * v x + δ * |v x|) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ δ⁻¹ * Real.exp (u x + t₀ * v x + 2 * δ * |v x|) := by
        gcongr δ⁻¹ * Real.exp ?_
        linarith
      _ ≤ _ := by
        gcongr
        rcases le_total 0 (v x) with h | h
        · rw [abs_of_nonneg h,
            show u x + t₀ * v x + 2 * δ * v x = u x + (t₀ + 2 * δ) * v x by ring]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos h,
            show u x + t₀ * v x + 2 * δ * -v x = u x + (t₀ - 2 * δ) * v x by ring]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hderiv (x : X) (t : ℝ) :
      HasDerivAt (fun t ↦ Real.exp (u x + t * v x)) (v x * Real.exp (u x + t * v x)) t := by
    have := (((hasDerivAt_id' t).mul_const (v x)).const_add (u x)).exp
    convert this using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ v x * Real.exp (u x + t * v x))
    (bound := fun x ↦
      δ⁻¹ * (Real.exp (u x + (t₀ + 2 * δ) * v x) + Real.exp (u x + (t₀ - 2 * δ) * v x)))
    (Metric.ball_mem_nhds t₀ hδ0)
    (hint.mono fun _ h ↦ h.aestronglyMeasurable)
    hint₀ (hv.mul hint₀.aestronglyMeasurable)
    (ae_of_all _ fun x t ht ↦ hbound x t ht) ((hint_add.add hint_sub).const_mul _)
    (ae_of_all _ fun x t _ ↦ hderiv x t)).2

end TauCeti
