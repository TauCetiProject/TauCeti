/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Minimizer
public import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
import TauCeti.Analysis.PDE.Vortex.Background
import TauCeti.Analysis.PDE.Vortex.EulerLagrange
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.SpecialFunctions.Exp.Modular

/-!
# Weak solutions of the reduced vortex equation are the minimizer

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`. The minimizer `w_P = TauCeti.Vortex.reducedMinimizer P` of Taubes's
functional `I` on `H¹(ℂ)` (`TauCeti.Vortex.sobolevReducedFunctional`) is a weak solution of the
reduced vortex equation `Δw = (exp (2w) h - 1) / 8 + g`
(`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`). This file proves the
converse: if `u ∈ H¹(ℂ)` satisfies

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`

for every smooth compactly supported `φ`, then `u = w_P`
(`TauCeti.Vortex.eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero`). So
`w_P` is the unique weak solution of the reduced equation in `H¹(ℂ)`
(`TauCeti.Vortex.eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero`).

The proof is by convexity, in three steps.

1. **The solution is bounded and the source is square integrable.** The source
   `f = TauCeti.Vortex.reducedSource P u = (exp (2u) h - 1) / 8 + g` is square integrable
   (`TauCeti.Vortex.memLp_reducedSource`), and `u` agrees almost everywhere with a continuous
   function vanishing at infinity
   (`TauCeti.Vortex.exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource`), so
   `u ≤ M` for some `M`. This makes `I(u)` finite, by
   `Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq`.
2. **The equation holds against all of `H¹(ℂ)`.** The left-hand side
   `⟪∇u, ∇v⟫ + ∫ f v` is a continuous linear function of `v ∈ H¹(ℂ)`, and it vanishes on test
   functions, which are dense in `H¹(ℂ)`
   (`TauCeti.W1p.inner_gradient_add_integral_mul_value_eq_zero`).
3. **Tangent inequality.** Each of the three terms of `I` lies above its tangent at `u`:
   `‖∇v‖² / 2 ≥ ‖∇u‖² / 2 + ⟪∇u, ∇(v - u)⟫` by expanding a square, and with
   `Φ(t) = exp (2t) - 1 - 2t`, `Φ(b) ≥ Φ(a) + 2 (exp (2a) - 1) (b - a)` because
   `exp (2(b - a)) ≥ 1 + 2 (b - a)` (`Real.exp_two_mul_sub_one_sub_two_mul_add_mul_le`). Adding
   them gives `I(v) ≥ I(u) + ⟪∇u, ∇(v - u)⟫ + ∫ f (v - u)`, and the last two terms cancel by
   step 2. So `u` minimizes `I`, and the minimizer is unique
   (`TauCeti.Vortex.eq_reducedMinimizer_iff`).

## Main results

* `TauCeti.Vortex.eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero`: a weak
  solution of the reduced vortex equation in `H¹(ℂ)` is the minimizer of Taubes's functional.
* `TauCeti.Vortex.eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero`:
  the minimizer is characterized in `H¹(ℂ)` by the weak reduced equation.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff Gradient RealInnerProductSpace

variable {P : Polynomial ℂ}

/-! ### Weak solutions minimize Taubes's functional -/

/-- The potential `∫ h (exp (2w) - 1 - 2w)` of Taubes's functional lies above its tangent at `u`:
its value at `v` is at least its value at `u` plus `2 ∫ h (exp (2u) - 1) (v - u)`. -/
private theorem integral_potential_add_le {u v : ℂ → ℝ}
    (hu : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * u z) - 1 - 2 * u z))
    (hv : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * v z) - 1 - 2 * v z))
    (hB : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * u z) - 1) * (v z - u z)) :
    (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * u z) - 1 - 2 * u z)) +
        2 * ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * u z) - 1) *
          (v z - u z) ≤
      ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * v z) - 1 - 2 * v z) := by
  rw [← integral_const_mul, ← integral_add hu (hB.const_mul 2)]
  refine integral_mono (hu.add (hB.const_mul 2)) hv fun z ↦ ?_
  have h0 : 0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    simpa only [backgroundWeight_def] using backgroundWeight_nonneg P.eval z
  have ht := mul_le_mul_of_nonneg_left
    (Real.exp_two_mul_sub_one_sub_two_mul_add_mul_le (u z) (v z)) h0
  simp only
  linarith

/-- For `u, v ∈ H¹(ℂ)`, `h (exp (2u) - 1) (v - u)` is integrable, where `h = ‖P‖² / (1 + ‖P‖²)`. -/
private theorem integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_mul_sub
    (u v : W1p (volume : Measure ℂ) ⊤ 2) :
    Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1) * (W1p.value v z - W1p.value u z) := by
  simpa only [backgroundWeight_def, Pi.mul_def, Pi.sub_apply] using
    (memLp_backgroundWeight_mul_exp_two_mul_sub_one P.continuous u).integrable_mul
      ((W1p.memLp_value v).sub (W1p.memLp_value u))

/-- The zeroth-order term of the weak reduced equation in the direction `v - u` splits as
`(1 / 8) ∫ h (exp (2u) - 1) (v - u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) (v - u)`. -/
private theorem integral_reducedSource_mul_value_sub (hm : 0 < P.natDegree)
    (u v : W1p (volume : Measure ℂ) ⊤ 2) :
    (∫ z, reducedSource P (W1p.value u) z * W1p.value (v - u) z) =
      (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * W1p.value u z) - 1) *
        (W1p.value v z - W1p.value u z)) / 8 +
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * (W1p.value v z - W1p.value u z) := by
  have hsub : (W1p.value (v - u) : ℂ → ℝ) =ᵐ[volume] fun z ↦ W1p.value v z - W1p.value u z := by
    have h := W1p.value_sub_ae v u
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans (ae_of_all _ fun _ ↦ rfl)
  have hd : MemLp (fun z ↦ W1p.value v z - W1p.value u z) 2 :=
    (W1p.memLp_value v).sub (W1p.memLp_value u)
  have hB := integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_mul_sub (P := P) u v
  have hC : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * (W1p.value v z - W1p.value u z) :=
    (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).integrable_mul hd
  rw [← integral_div, ← integral_add (hB.div_const 8) hC]
  refine integral_congr_ae (hsub.mono fun z hz ↦ ?_)
  simp only [hz, reducedSource_eq_add_sub_inv_div_eight]
  ring

/-- **The tangent inequality for Taubes's functional.** At `u ∈ H¹(ℂ)` which solves the weak
reduced equation, `I(u) ≤ I(v)` for every `v ∈ H¹(ℂ)`: each term of `I` lies above its tangent at
`u`, and the sum of the tangent terms is the weak equation in the direction `v - u`. -/
private theorem sobolevReducedFunctional_le_of_forall_integral_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
  -- `u` has a continuous representative vanishing at infinity, so it is bounded above.
  obtain ⟨w, hw⟩ := exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource hm hweak
  have hu := integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_sub_two_mul (P := P)
    (norm_nonneg w.toBCF) (hw.mono fun z hz ↦ by rw [hz]; exact w.toBCF.apply_le_norm z)
  by_cases hv : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)
  swap
  · rw [sobolevReducedFunctional_eq_top hv]
    exact le_top
  rw [sobolevReducedFunctional_eq_coe hu, sobolevReducedFunctional_eq_coe hv,
    EReal.coe_le_coe_iff]
  have hd : MemLp (fun z ↦ W1p.value v z - W1p.value u z) 2 :=
    (W1p.memLp_value v).sub (W1p.memLp_value u)
  have hc := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  -- The weak equation in the direction `v - u`, split into its two zeroth-order terms.
  have hE :=
    W1p.inner_gradient_add_integral_mul_value_eq_zero (memLp_reducedSource hm u) hweak (v - u)
  rw [integral_reducedSource_mul_value_sub hm, W1p.gradient_sub] at hE
  -- The Dirichlet energy lies above its tangent.
  have hG : ‖W1p.gradient u‖ ^ 2 / 2 + ⟪W1p.gradient u, W1p.gradient v - W1p.gradient u⟫ ≤
      ‖W1p.gradient v‖ ^ 2 / 2 := by
    have h := norm_add_sq_real (W1p.gradient u) (W1p.gradient v - W1p.gradient u)
    rw [add_sub_cancel] at h
    nlinarith [sq_nonneg ‖W1p.gradient v - W1p.gradient u‖]
  -- So does the potential.
  have hP := integral_potential_add_le hu hv
    (integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_mul_sub u v)
  -- The linear term is linear.
  have hL : (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z) =
      (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * (W1p.value v z - W1p.value u z) := by
    have hcu : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z :=
      hc.integrable_mul (W1p.memLp_value u)
    have hcd : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * (W1p.value v z - W1p.value u z) :=
      hc.integrable_mul hd
    rw [← integral_add hcu hcd]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  linarith

/-- **Weak solutions of the reduced vortex equation are the minimizer.** Let `P` have degree at
least one, and put `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. If `u ∈ H¹(ℂ)` is a
weak solution of the reduced vortex equation `Δu = (exp (2u) h - 1) / 8 + g`, that is

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`

for every smooth compactly supported `φ`, then `u` is the minimizer
`TauCeti.Vortex.reducedMinimizer P` of Taubes's functional. -/
theorem eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0) :
    u = reducedMinimizer P :=
  (eq_reducedMinimizer_iff hm).2 <| sobolevReducedFunctional_le_of_forall_integral_eq_zero hm hweak

/-- **The weak reduced equation characterizes the minimizer.** Let `P` have degree at least one.
An element `u ∈ H¹(ℂ)` is the minimizer `TauCeti.Vortex.reducedMinimizer P` of Taubes's functional
exactly when it is a weak solution of the reduced vortex equation
`Δu = (exp (2u) h - 1) / 8 + g`, with `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`,
tested against smooth compactly supported functions. -/
theorem eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2} :
    u = reducedMinimizer P ↔ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0 := by
  refine ⟨?_, eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero hm⟩
  rintro rfl φ hφ hφc
  simpa only [reducedSource_eq_exp_mul_sub_one_div_eight_add] using
    integral_inner_gradient_add_integral_mul_eq_zero hm
      (forall_sobolevReducedFunctional_reducedMinimizer_le hm) (hφ.of_le (by simp)) hφc

end TauCeti.Vortex
