/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on a half-line `u ≥ a` by `exp (-u (sigma - 1))` leaves the integral of an
integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on the
half-line uniformly in `sigma ∈ [1, 2]`, so dominated convergence applies.

Conversely, increasing the damping rate from `σ` to `x ≥ σ` multiplies the integrand by
`e^{-(x-σ)t} ≤ e^{-(x-σ)δ}` for `t ≥ δ`. This preserves integrability on a right half-line, and on
`(δ, ∞)` it gains the factor `e^{-(x-σ)δ}`: this bounds the tail of a Laplace integral.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_setIntegral_exp_smul`: the damped integral converges to the undamped one as
  `sigma` decreases to `1`.
* `TauCeti.exp_neg_sub_mul_le_of_le`: `e^{-(x-σ)t} ≤ e^{-(x-σ)δ}` for `σ ≤ x` and `δ ≤ t`.
* `MeasureTheory.IntegrableOn.exp_neg_mul_smul_of_le`: if `e^{-σt} G(t)` is integrable on
  `(0, ∞)`, so is the more strongly damped `e^{-xt} G(t)` for every `x ≥ σ`.
* `TauCeti.norm_setIntegral_Ioi_exp_neg_mul_smul_le`: on `(δ, ∞)` the extra damping
  `e^{-(x-σ)t}` is at most `e^{-(x-σ)δ}`, which bounds the tail of a Laplace integral.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E}
  {a : ℝ}

/-- As `sigma` decreases to `1`, the one-sided Laplace transform
`∫ u in Ici a, exp (-u (sigma - 1)) • f u` of a function integrable on the half-line `u ≥ a`
converges to its undamped integral. -/
theorem tendsto_setIntegral_exp_smul (hf : IntegrableOn f (Ici a) μ) :
    Tendsto (fun sigma : ℝ ↦ ∫ u in Ici a, Real.exp (-u * (sigma - 1)) • f u ∂μ)
      (𝓝[≥] 1) (𝓝 (∫ u in Ici a, f u ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ Real.exp (max 0 (-a)) * ‖f u‖)
    (.of_forall fun sigma ↦ (Continuous.aestronglyMeasurable (by fun_prop)).smul hf.1) ?_
    (hf.norm.const_mul _) (.of_forall fun u ↦ ?_)
  · filter_upwards [Icc_mem_nhdsGE (by norm_num : (1 : ℝ) < 2)] with sigma ⟨h1, h2⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u (hu : a ≤ u)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    gcongr
    rcases le_total 0 u with h | h <;> nlinarith [le_max_left 0 (-a), le_max_right 0 (-a)]
  · have hexp : Tendsto (fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))) (𝓝 1) (𝓝 1) :=
      (by fun_prop : Continuous fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))).tendsto' 1 1 (by simp)
    simpa using (hexp.mono_left nhdsWithin_le_nhds).smul_const (f u)

/-- Raising the damping rate from `σ` to `x ≥ σ` multiplies by `e^{-(x-σ)t}`, which is at most
`e^{-(x-σ)δ}` for `t ≥ δ`. -/
theorem exp_neg_sub_mul_le_of_le {σ x δ t : ℝ} (hx : σ ≤ x) (ht : δ ≤ t) :
    Real.exp (-(x - σ) * t) ≤ Real.exp (-(x - σ) * δ) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (by linarith))

/-- If `t ↦ e^{-σt} G(t)` is integrable on `(0, ∞)`, then so is `t ↦ e^{-xt} G(t)` for every
`x ≥ σ`. -/
theorem _root_.MeasureTheory.IntegrableOn.exp_neg_mul_smul_of_le {G : ℝ → E} {σ x : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0)) (hx : σ ≤ x) :
    IntegrableOn (fun t => Real.exp (-x * t) • G t) (Ioi 0) := by
  have h := hint.bdd_smul 1 (φ := fun t => Real.exp (-(x - σ) * t))
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(x - σ) * t)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      simpa using exp_neg_sub_mul_le_of_le hx ht.le)
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply', smul_smul, ← Real.exp_add]
  ring_nf

/-- The part of a Laplace integral beyond `δ`: if `t ↦ e^{-σt} G(t)` is integrable on `(δ, ∞)`
and `x ≥ σ`, then `‖∫_δ^∞ e^{-xt} G(t) dt‖ ≤ e^{-(x-σ)δ} ∫_δ^∞ ‖e^{-σt} G(t)‖ dt`. -/
theorem norm_setIntegral_Ioi_exp_neg_mul_smul_le {G : ℝ → E} {σ x δ : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi δ)) (hx : σ ≤ x) :
    ‖∫ t in Ioi δ, Real.exp (-x * t) • G t‖ ≤
      Real.exp (-(x - σ) * δ) * ∫ t in Ioi δ, ‖Real.exp (-σ * t) • G t‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.norm.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : δ < t)
  have hsplit : Real.exp (-x * t) = Real.exp (-(x - σ) * t) * Real.exp (-σ * t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le, hsplit, mul_assoc]
  exact mul_le_mul_of_nonneg_right (exp_neg_sub_mul_le_of_le hx ht.le) (by positivity)

end TauCeti
