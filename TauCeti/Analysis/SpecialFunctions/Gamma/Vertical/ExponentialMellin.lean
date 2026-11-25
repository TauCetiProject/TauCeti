/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Integrability

/-!
# Exponential Mellin inversion

For `c > 0` and `Re w > 0`, the Cahen–Mellin integral is
`∫ Γ(c + i y) w^{-(c + i y)} dy = 2π e^{-w}`, with the principal power. For real `w > 0` this is
Mellin inversion for `Γ` (`Complex.integral_cpow_neg_mul_Gamma`). Since
`‖w^{-(c + i y)}‖ = ‖w‖^{-c} e^{y arg w}` and `|arg w| < π / 2`, the exponential decay of `Γ` on
vertical lines dominates the integrand locally uniformly in `w`, so the integral is holomorphic
on the right half-plane, and the identity theorem extends the formula from the positive reals.

## Main results

* `Asymptotics.integrable_Gamma_mul_cpow_neg`: the Cahen–Mellin integrand is integrable for
  `Re w > 0` on every vertical line `Re s = c` avoiding the poles of `Γ`.
* `Asymptotics.integral_Gamma_mul_cpow_neg`: for `c > 0` the Cahen–Mellin integral equals
  `2π e^{-w}`.

## References

* [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1): Euler's integral, the Mellin transform of
  `e^{-t}`.
* [DLMF §2.5](https://dlmf.nist.gov/2.5): Mellin transform methods, which use this kernel.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Gamma/Integrals/ExponentialMellin.lean`, which goes through a Fourier–Laplace integral in
`log w` on a horizontal strip instead of working on the right half-plane.
-/

public section

open Set Filter MeasureTheory Topology
open scoped Real
open Complex

namespace Asymptotics

/-- If `|arg w| ≤ θ`, the Cahen–Mellin integrand is bounded by `‖w‖^{-c}` times
`‖Γ(c + i y) e^{θ |y|}‖`. -/
private lemma norm_Gamma_mul_cpow_neg_le {c θ : ℝ} {w : ℂ} (hθ : |w.arg| ≤ θ) (y : ℝ) :
    ‖Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I))‖ ≤
      ‖w‖ ^ (-c) * ‖Gamma (c + y * I) * (Real.exp (θ * |y|) : ℂ)‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · -- `0 ^ s = 0` for `s ≠ 0`, and `Γ 0 = 0` takes care of `s = 0`
    rcases eq_or_ne ((c : ℂ) + y * I) 0 with h | h
    · simp [h]
    · rw [zero_cpow (neg_ne_zero.mpr h), mul_zero, norm_zero]
      positivity
  rw [norm_mul, norm_mul, norm_cpow_of_ne_zero hw, norm_real, Real.norm_of_nonneg (by positivity)]
  have hre : (-((c : ℂ) + y * I)).re = -c := by simp
  have him : (-((c : ℂ) + y * I)).im = -y := by simp
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg, mul_neg, neg_neg, mul_left_comm]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (norm_nonneg _)) (by positivity)
  calc w.arg * y ≤ |w.arg * y| := le_abs_self _
    _ = |w.arg| * |y| := abs_mul _ _
    _ ≤ θ * |y| := by gcongr

/-- On a line `Re s = c` avoiding the poles of `Γ`, `Γ(c + i y) e^{θ |y|}` is integrable for
`θ < π / 2`. -/
private lemma integrable_Gamma_mul_exp {c θ : ℝ} (hc : ∀ n : ℕ, c ≠ -n) (hθ : θ < π / 2) :
    Integrable fun y : ℝ ↦ Gamma (c + y * I) * (Real.exp (θ * |y|) : ℂ) := by
  simpa [VerticalIntegrable] using TauCeti.verticalIntegrable_Gamma_mul_exp_mul_abs_im hc hθ

/-- The Cahen–Mellin integrand `y ↦ Γ(c + i y) w^{-(c + i y)}` is continuous on a line
`Re s = c` avoiding the poles of `Γ`. -/
private lemma continuous_Gamma_mul_cpow_neg {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n) (w : ℂ) :
    Continuous fun y : ℝ ↦ Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I)) :=
  (continuous_Gamma_add_mul_I fun n ↦ by rw [ofReal_re]; exact hc n).mul
    ((by fun_prop : Continuous fun y : ℝ ↦ -((c : ℂ) + y * I)).const_cpow (Or.inr fun y h ↦
      -- the exponent has real part `-c ≠ 0`
      hc 0 (by simpa using congrArg re h)))

/-- The Cahen–Mellin integrand `y ↦ Γ(c + i y) w^{-(c + i y)}` is integrable for `Re w > 0` on
every line `Re s = c` avoiding the poles `0, -1, -2, …` of `Γ`. -/
theorem integrable_Gamma_mul_cpow_neg {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n) {w : ℂ} (hw : 0 < w.re) :
    Integrable fun y : ℝ ↦ Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I)) :=
  ((integrable_Gamma_mul_exp hc (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))).norm.const_mul
    (‖w‖ ^ (-c))).mono'
    (continuous_Gamma_mul_cpow_neg hc w).aestronglyMeasurable
    (Eventually.of_forall (norm_Gamma_mul_cpow_neg_le le_rfl))

/-- On a line `Re s = c` avoiding the poles of `Γ`, the Cahen–Mellin integral is holomorphic in
`w` on the right half-plane. -/
private lemma analyticOnNhd_integral_Gamma_mul_cpow_neg {c : ℝ} (hc : ∀ n : ℕ, c ≠ -n) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ ∫ y : ℝ, Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I)))
      {w | 0 < w.re} := by
  refine TauCeti.analyticOnNhd_integral_of_dominated (isOpen_lt continuous_const continuous_re)
    (fun w _ ↦ (continuous_Gamma_mul_cpow_neg hc w).aestronglyMeasurable)
    (fun w₀ hw₀ ↦ ?_) (Eventually.of_forall fun y w hw ↦ ?_)
  · -- near `w₀`, `‖w₀‖ / 2 < ‖w‖ < 2 ‖w₀‖` and `|arg w| < θ` for a fixed `θ < π / 2`
    have hw₀' : 0 < ‖w₀‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hw₀)
    have harg : |w₀.arg| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw₀)
    set θ := (|w₀.arg| + π / 2) / 2
    have hnorm : ∀ᶠ w in 𝓝 w₀, ‖w‖ ∈ Ioo (1 / 2 * ‖w₀‖) (2 * ‖w₀‖) :=
      continuous_norm.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have harg' : ∀ᶠ w in 𝓝 w₀, |w.arg| < θ :=
      (continuousAt_arg (mem_slitPlane_iff.mpr (Or.inl hw₀))).abs.eventually
        (gt_mem_nhds (by dsimp [θ]; linarith))
    refine ⟨_, hnorm.and harg', fun y ↦ max ((1 / 2) ^ (-c)) (2 ^ (-c)) * ‖w₀‖ ^ (-c) *
      ‖Gamma (c + y * I) * (Real.exp (θ * |y|) : ℂ)‖,
      (integrable_Gamma_mul_exp hc (by dsimp [θ]; linarith)).norm.const_mul _,
      Eventually.of_forall fun y w hw ↦ ?_⟩
    refine (norm_Gamma_mul_cpow_neg_le hw.2.le y).trans (mul_le_mul_of_nonneg_right ?_
      (norm_nonneg _))
    exact Real.rpow_le_max_mul_rpow (by norm_num) hw₀'.le hw.1.1.le hw.1.2.le (-c)
  · exact ((differentiableAt_id.cpow_const (mem_slitPlane_iff.mpr (Or.inl hw))).const_mul
      _).differentiableWithinAt

/-- **Exponential Mellin inversion** (the Cahen–Mellin integral). For `c > 0` and `Re w > 0`,
`y ↦ Γ(c + i y) w^{-(c + i y)}` is integrable and `∫ Γ(c + i y) w^{-(c + i y)} dy = 2π e^{-w}`,
with the principal power. -/
theorem integral_Gamma_mul_cpow_neg {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun y : ℝ ↦ Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I))) ∧
      ∫ y : ℝ, Gamma (c + y * I) * w ^ (-((c : ℂ) + y * I)) = 2 * π * cexp (-w) := by
  have hc' : ∀ n : ℕ, c ≠ -n := fun n ↦ ((neg_nonpos.mpr n.cast_nonneg).trans_lt hc).ne'
  refine ⟨integrable_Gamma_mul_cpow_neg hc' hw, ?_⟩
  have hU : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦ 2 * π * cexp (-w)) {w | 0 < w.re} :=
    (by fun_prop : Differentiable ℂ fun w : ℂ ↦ 2 * π * cexp (-w)).differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const continuous_re)
  refine (analyticOnNhd_integral_Gamma_mul_cpow_neg hc').eqOn_of_preconnected_of_frequently_eq hg
    hU (z₀ := 1) (by simp) ?_ hw
  -- the formula holds on the positive reals, which accumulate at `1`
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    simpa using Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (x := 1)
      fun _ _ ↦ by simp_all
  refine hreal.frequently (eventually_nhdsWithin_of_eventually_nhds
    ((lt_mem_nhds one_pos).mono fun x (hx : 0 < x) ↦ ?_)).frequently
  simp_rw [mul_comm (Gamma _)]
  rw [integral_cpow_neg_mul_Gamma hc hx, ofReal_exp, ofReal_neg]

end Asymptotics
