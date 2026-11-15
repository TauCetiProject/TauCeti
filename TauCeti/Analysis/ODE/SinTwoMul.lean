/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.ODE.ExistUnique
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The equation `ψ' = κ sin (2 ψ)`

The autonomous scalar equation `ψ' = κ sin (2 ψ)` is the gradient flow of `-(κ / 2) cos (2 ψ)` on
the line. Its equilibria are the multiples of `π / 2`; for `κ > 0` the points `j π` repel and the
points `π / 2 + j π` attract. Inside `(-π / 2, π / 2)` its solutions are explicit: the tangent of a
solution grows like `e^{2 κ s}`, so the solution with `ψ s₀ = ψ₀` is
`arctan (tan ψ₀ e^{2 κ (s - s₀)})`.

These are the slice dynamics of a continuation of `δ cos (2 (θ - r))` on the circle, near a
critical point of a fixed slice.

## Main declarations

* `TauCeti.hasDerivAt_arctan_mul_exp` and `TauCeti.eqOn_arctan_mul_exp_of_hasDerivAt`: the
  solutions inside `(-π / 2, π / 2)`.
* `TauCeti.eqOn_zero_of_hasDerivAt_sin_two_mul_of_eq_zero`: a solution vanishing once vanishes
  everywhere.
* `TauCeti.tendsto_atBot_of_hasDerivAt_sin_two_mul` and
  `TauCeti.tendsto_atTop_of_hasDerivAt_sin_two_mul`: convergence to the equilibrium `0`, backward
  for `κ > 0` and forward for `κ < 0`.
* `TauCeti.eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul` and
  `TauCeti.eqOn_zero_of_tendsto_atBot_of_hasDerivAt_sin_two_mul`: only the constant solution
  converges to `0` forward for `κ ≥ 0`, or backward for `κ ≤ 0`.
-/

public section

open Filter Real Set Topology

namespace TauCeti

variable {κ s₀ : ℝ} {ψ : ℝ → ℝ} {I : Set ℝ}

/-- **The explicit flow of `ψ' = κ sin (2 ψ)`.** For every `c`, the function
`s ↦ arctan (c e^{2 κ (s - s₀)})` solves `ψ' = κ sin (2 ψ)`: its tangent grows like `e^{2 κ s}`. -/
theorem hasDerivAt_arctan_mul_exp (κ c s₀ s : ℝ) :
    HasDerivAt (fun s ↦ arctan (c * exp (2 * κ * (s - s₀))))
      (κ * sin (2 * arctan (c * exp (2 * κ * (s - s₀))))) s := by
  have he : HasDerivAt (fun s ↦ c * exp (2 * κ * (s - s₀)))
      (c * exp (2 * κ * (s - s₀)) * (2 * κ)) s :=
    ((((hasDerivAt_id' s).sub_const s₀).const_mul (2 * κ)).exp.const_mul c).congr_deriv (by ring)
  refine he.arctan.congr_deriv ?_
  rw [sin_two_mul_arctan]
  field_simp

/-- **The solutions of `ψ' = κ sin (2 ψ)` inside `(-π / 2, π / 2)`.** On a preconnected set `I`,
a solution with `|ψ s₀| < π / 2` at some `s₀ ∈ I` is `arctan (tan (ψ s₀) e^{2 κ (s - s₀)})`. -/
theorem eqOn_arctan_mul_exp_of_hasDerivAt (hI : IsPreconnected I) (hs₀ : s₀ ∈ I)
    (hψ : ∀ s ∈ I, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    EqOn ψ (fun s ↦ arctan (tan (ψ s₀) * exp (2 * κ * (s - s₀)))) I := by
  refine hI.ode_eqOn_of_contDiffAt (V := fun p : ℝ × ℝ ↦ κ * sin (2 * p.2))
    (fun _ _ ↦ by fun_prop) hs₀ ?_ (fun s hs ↦ (hψ s hs).hasDerivWithinAt)
    (fun s _ ↦ (hasDerivAt_arctan_mul_exp κ _ s₀ s).hasDerivWithinAt)
  rw [abs_lt] at h
  simp [arctan_tan h.1 h.2]

/-- A solution of `ψ' = κ sin (2 ψ)` on a preconnected set vanishing at one point vanishes on the
whole set. -/
theorem eqOn_zero_of_hasDerivAt_sin_two_mul_of_eq_zero (hI : IsPreconnected I) (hs₀ : s₀ ∈ I)
    (hψ : ∀ s ∈ I, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : ψ s₀ = 0) : EqOn ψ 0 I := by
  intro s hs
  rw [eqOn_arctan_mul_exp_of_hasDerivAt hI hs₀ hψ (by rw [h, abs_zero]; positivity) hs]
  simp [h]

/-- Reversing time turns a solution of `ψ' = κ sin (2 ψ)` into a solution of
`ψ' = -κ sin (2 ψ)`. -/
private theorem hasDerivAt_comp_neg {s : ℝ} (hψ : HasDerivAt ψ (κ * sin (2 * ψ (-s))) (-s)) :
    HasDerivAt (fun s ↦ ψ (-s)) (-κ * sin (2 * ψ (-s))) s := by
  simpa [Function.comp_def, neg_mul] using hψ.comp s (hasDerivAt_neg s)

/-- **Backward convergence to a repelling equilibrium.** For `κ > 0`, a solution of
`ψ' = κ sin (2 ψ)` for `s ≤ s₀` with `|ψ s₀| < π / 2` tends to `0` at `-∞`. -/
theorem tendsto_atBot_of_hasDerivAt_sin_two_mul (hκ : 0 < κ)
    (hψ : ∀ s ≤ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    Tendsto ψ atBot (𝓝 0) := by
  have hlin : Tendsto (fun s ↦ 2 * κ * (s - s₀)) atBot atBot := by
    simpa [sub_eq_add_neg] using
      (tendsto_atBot_add_const_right _ (-s₀) tendsto_id).const_mul_atBot (by positivity : 0 < 2 * κ)
  have hlim : Tendsto (fun s ↦ arctan (tan (ψ s₀) * exp (2 * κ * (s - s₀)))) atBot (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_arctan.tendsto _).comp
      ((tendsto_exp_atBot.comp hlin).const_mul (tan (ψ s₀)))
  refine hlim.congr' ?_
  filter_upwards [eventually_le_atBot s₀] with s hs
  exact (eqOn_arctan_mul_exp_of_hasDerivAt isPreconnected_Iic self_mem_Iic hψ h hs).symm

/-- **Forward convergence to an attracting equilibrium.** For `κ < 0`, a solution of
`ψ' = κ sin (2 ψ)` for `s ≥ s₀` with `|ψ s₀| < π / 2` tends to `0` at `+∞`. -/
theorem tendsto_atTop_of_hasDerivAt_sin_two_mul (hκ : κ < 0)
    (hψ : ∀ s ≥ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : |ψ s₀| < π / 2) :
    Tendsto ψ atTop (𝓝 0) := by
  have := tendsto_atBot_of_hasDerivAt_sin_two_mul (neg_pos.2 hκ) (s₀ := -s₀)
    (fun s hs ↦ hasDerivAt_comp_neg (hψ _ (le_neg.1 hs))) (by rwa [neg_neg])
  simpa [Function.comp_def] using this.comp tendsto_neg_atTop_atBot

/-- **Only the constant solution converges forward to `0` for `κ ≥ 0`.** A solution of
`ψ' = κ sin (2 ψ)` for `s ≥ s₀` tending to `0` at `+∞` vanishes for `s ≥ s₀`. For `κ > 0` this is
the repulsion of the equilibrium `0`; for `κ = 0` every solution is constant. -/
theorem eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul (hκ : 0 ≤ κ)
    (hψ : ∀ s ≥ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : Tendsto ψ atTop (𝓝 0)) :
    EqOn ψ 0 (Ici s₀) := by
  obtain ⟨s₁, hs₁, hψ₁⟩ := ((eventually_ge_atTop s₀).and
    (h.abs.eventually_lt_const (by rw [abs_zero]; positivity : |(0 : ℝ)| < π / 2))).exists
  have heq := eqOn_arctan_mul_exp_of_hasDerivAt isPreconnected_Ici self_mem_Ici
    (fun s hs ↦ hψ s (hs₁.trans hs)) hψ₁
  -- Along the explicit solution, `tan (ψ s₁) e^{2 κ (s - s₁)} → 0`, while the factor is `≥ 1`.
  have ht : Tendsto (fun s ↦ tan (ψ s₁) * exp (2 * κ * (s - s₁))) atTop (𝓝 0) := by
    have h' := h.congr' (by filter_upwards [eventually_ge_atTop s₁] with s hs using heq hs)
    simpa [Function.comp_def, tan_arctan] using
      (continuousAt_tan.2 (by simp : cos 0 ≠ 0)).tendsto.comp h'
  have hc : tan (ψ s₁) = 0 := by
    refine abs_eq_zero.1 (le_antisymm (ge_of_tendsto (by simpa using ht.abs) ?_) (abs_nonneg _))
    filter_upwards [eventually_ge_atTop s₁] with s hs
    exact le_mul_of_one_le_right (abs_nonneg _)
      (one_le_exp (mul_nonneg (by positivity) (sub_nonneg.2 hs)))
  refine eqOn_zero_of_hasDerivAt_sin_two_mul_of_eq_zero isPreconnected_Ici hs₁ hψ ?_
  rw [abs_lt] at hψ₁
  rw [← arctan_tan hψ₁.1 hψ₁.2, hc, arctan_zero]

/-- **Only the constant solution converges backward to `0` for `κ ≤ 0`.** A solution of
`ψ' = κ sin (2 ψ)` for `s ≤ s₀` tending to `0` at `-∞` vanishes for `s ≤ s₀`. For `κ < 0` this is
the attraction of the equilibrium `0`; for `κ = 0` every solution is constant. -/
theorem eqOn_zero_of_tendsto_atBot_of_hasDerivAt_sin_two_mul (hκ : κ ≤ 0)
    (hψ : ∀ s ≤ s₀, HasDerivAt ψ (κ * sin (2 * ψ s)) s) (h : Tendsto ψ atBot (𝓝 0)) :
    EqOn ψ 0 (Iic s₀) := by
  have := eqOn_zero_of_tendsto_atTop_of_hasDerivAt_sin_two_mul (neg_nonneg.2 hκ) (s₀ := -s₀)
    (fun s hs ↦ hasDerivAt_comp_neg (hψ _ (neg_le.1 hs)))
    (h.comp tendsto_neg_atTop_atBot)
  intro s hs
  simpa using this (neg_le_neg hs : -s₀ ≤ -s)

end TauCeti
