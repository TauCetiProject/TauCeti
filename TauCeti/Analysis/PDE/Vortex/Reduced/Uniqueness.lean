/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Minimizer
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
(`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`). This file proves the converse
for solutions bounded above: if `u ∈ H¹(ℂ)` satisfies `u ≤ M` almost everywhere and

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`

for every smooth compactly supported `φ`, then `u = w_P`
(`TauCeti.Vortex.eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero`). So
among the elements of `H¹(ℂ)` bounded above, `w_P` is characterized by the weak reduced equation
(`TauCeti.Vortex.eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero`).

A solution of the reduced equation obtained by other means, for instance in `H²(ℂ)`, which embeds
in the bounded functions, therefore agrees with Taubes's minimizer as soon as it satisfies the
equation.

The proof is by convexity, in three steps.

1. **The source is square integrable.** For `t ≤ M` with `M ≥ 0`,
   `|exp (2t) - 1| ≤ 2 exp (2M) |t|` (`Real.abs_exp_two_mul_sub_one_le_mul_abs`), so
   `h (exp (2u) - 1)` is dominated by a multiple of `|u|`.
   Since `(h - 1) / 8 + g` is square integrable
   (`TauCeti.Vortex.memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight`), so is the source
   `f = (exp (2u) h - 1) / 8 + g`. The same bound makes `I(u)` finite, by
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
  solution of the reduced vortex equation in `H¹(ℂ)` that is bounded above is the minimizer of
  Taubes's functional.
* `TauCeti.Vortex.eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero`:
  among the elements of `H¹(ℂ)` bounded above, the minimizer is characterized by the weak reduced
  equation.

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

/-! ### The source of the reduced equation -/

variable {P : Polynomial ℂ}

/-- For `u ∈ H¹(ℂ)` bounded above, `h (exp (2u) - 1)` is square integrable. -/
private theorem memLp_mul_exp_two_mul_sub_one {u : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ}
    (hM : 0 ≤ M) (huM : ∀ᵐ z, W1p.value u z ≤ M) :
    MemLp (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1)) 2 := by
  have hmeas : AEStronglyMeasurable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1) :=
    (((continuous_backgroundWeight P.continuous).congr
      (backgroundWeight_def _)).aestronglyMeasurable).mul
      ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (2 * t) - 1).comp_aestronglyMeasurable
        (W1p.memLp_value u).aestronglyMeasurable)
  refine ((W1p.memLp_value u).norm.const_mul (2 * Real.exp (2 * M))).of_le hmeas ?_
  filter_upwards [huM] with z hz
  have h0 : 0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    simpa only [backgroundWeight_def] using backgroundWeight_nonneg P.eval z
  have h1 : ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ≤ 1 := by
    simpa only [backgroundWeight_def] using (backgroundWeight_lt_one P.eval z).le
  have hpos : 0 ≤ 2 * Real.exp (2 * M) := by positivity
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h0, abs_of_nonneg hpos]
  exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans
    (Real.abs_exp_two_mul_sub_one_le_mul_abs hM hz)

/-- The source `(exp (2u) h - 1) / 8 + g` of the reduced equation is `h (exp (2u) - 1) / 8` plus
the coefficient `g - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's functional. -/
private theorem source_eq (P : Polynomial ℂ) (t : ℝ) (z : ℂ) :
    (Real.exp (2 * t) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 =
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * t) - 1) / 8 +
        (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) := by
  have h1 : (1 + ‖P.eval z‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- For `u ∈ H¹(ℂ)` bounded above, the source `(exp (2u) h - 1) / 8 + g` of the reduced
equation is square integrable. -/
private theorem memLp_source (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ}
    (hM : 0 ≤ M) (huM : ∀ᵐ z, W1p.value u z ≤ M) :
    MemLp (fun z ↦ (Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) /
      8 + 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) 2 := by
  have h := ((memLp_mul_exp_two_mul_sub_one (P := P) hM huM).const_mul (8⁻¹ : ℝ)).add
    (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm)
  convert h using 1
  funext z
  rw [source_eq P _ z, Pi.add_apply]
  ring

/-! ### Bounded-above weak solutions minimize Taubes's functional -/

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

/-- The zeroth-order term of the weak reduced equation in the direction `v - u` splits as
`(1 / 8) ∫ h (exp (2u) - 1) (v - u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) (v - u)`. -/
private theorem integral_source_mul_value_sub (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ} (hM : 0 ≤ M) (huM : ∀ᵐ z, W1p.value u z ≤ M) :
    (∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * W1p.value (v - u) z) =
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
  have hB : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1) * (W1p.value v z - W1p.value u z) :=
    (memLp_mul_exp_two_mul_sub_one hM huM).integrable_mul hd
  have hC : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * (W1p.value v z - W1p.value u z) :=
    (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).integrable_mul hd
  rw [← integral_div, ← integral_add (hB.div_const 8) hC]
  refine integral_congr_ae (hsub.mono fun z hz ↦ ?_)
  dsimp only
  rw [hz, source_eq P]
  ring

/-- **The tangent inequality for Taubes's functional.** At `u ∈ H¹(ℂ)` bounded above which solves
the weak reduced equation, `I(u) ≤ I(v)` for every `v ∈ H¹(ℂ)`: each term of `I` lies above its
tangent at `u`, and the sum of the tangent terms is the weak equation in the direction `v - u`. -/
private theorem sobolevReducedFunctional_le_of_forall_integral_eq_zero (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ} (hM : 0 ≤ M) (huM : ∀ᵐ z, W1p.value u z ≤ M)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
          2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z = 0)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
  have hu := integrable_norm_eval_sq_div_mul_exp_two_mul_sub_one_sub_two_mul (P := P) hM huM
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
    W1p.inner_gradient_add_integral_mul_value_eq_zero (memLp_source hm hM huM) hweak (v - u)
  rw [integral_source_mul_value_sub hm hM huM, W1p.gradient_sub] at hE
  -- The Dirichlet energy lies above its tangent.
  have hG : ‖W1p.gradient u‖ ^ 2 / 2 + ⟪W1p.gradient u, W1p.gradient v - W1p.gradient u⟫ ≤
      ‖W1p.gradient v‖ ^ 2 / 2 := by
    have h := norm_add_sq_real (W1p.gradient u) (W1p.gradient v - W1p.gradient u)
    rw [add_sub_cancel] at h
    nlinarith [sq_nonneg ‖W1p.gradient v - W1p.gradient u‖]
  -- So does the potential.
  have hP := integral_potential_add_le hu hv
    ((memLp_mul_exp_two_mul_sub_one hM huM).integrable_mul hd)
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

/-- **Bounded-above weak solutions of the reduced vortex equation are the minimizer.** Let `P`
have degree at least one, and put `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. If
`u ∈ H¹(ℂ)` is bounded above almost everywhere and is a weak solution of the reduced vortex
equation `Δu = (exp (2u) h - 1) / 8 + g`, that is

`∫ ⟪∇u, ∇φ⟫ + ∫ ((exp (2u) h - 1) / 8 + g) φ = 0`

for every smooth compactly supported `φ`, then `u` is the minimizer
`TauCeti.Vortex.reducedMinimizer P` of Taubes's functional. -/
theorem eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ}
    (huM : ∀ᵐ z, W1p.value u z ≤ M)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
          2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z = 0) :
    u = reducedMinimizer P :=
  (eq_reducedMinimizer_iff hm).2 <|
    sobolevReducedFunctional_le_of_forall_integral_eq_zero hm (le_max_right M 0)
      (huM.mono fun _ hz ↦ hz.trans (le_max_left M 0)) hweak

/-- **The weak reduced equation characterizes the minimizer.** Let `P` have degree at least one.
An element `u ∈ H¹(ℂ)` bounded above almost everywhere is the minimizer
`TauCeti.Vortex.reducedMinimizer P` of Taubes's functional exactly when it is a weak solution of
the reduced vortex equation `Δu = (exp (2u) h - 1) / 8 + g`, with `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`, tested against smooth compactly supported functions. -/
theorem eq_reducedMinimizer_iff_forall_integral_inner_gradient_add_integral_mul_eq_zero
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ}
    (huM : ∀ᵐ z, W1p.value u z ≤ M) :
    u = reducedMinimizer P ↔ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 +
          2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z = 0 := by
  refine ⟨?_, eq_reducedMinimizer_of_integral_inner_gradient_add_integral_mul_eq_zero hm huM⟩
  rintro rfl φ hφ hφc
  exact integral_inner_gradient_add_integral_mul_eq_zero hm
    (forall_sobolevReducedFunctional_reducedMinimizer_le hm) (hφ.of_le (by simp)) hφc

end TauCeti.Vortex
