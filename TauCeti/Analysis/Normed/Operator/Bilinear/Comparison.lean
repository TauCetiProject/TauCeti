/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform comparison of convergent coercive bilinear forms

If bilinear forms converge in operator norm to a coercive form, the square roots of their
diagonal values are eventually within any factor greater than one of the limiting values,
uniformly in the vector. The comparison holds on real seminormed spaces and along any filter;
the varying forms need not be symmetric or coercive.

This is the analytic estimate for sharp local pullback-metric comparisons used in
identifying Riemannian chart densities with Hausdorff volume.

## Main results

* `Real.sqrt_bounds_of_abs_sub_sq_le`: scalar square-root comparison from a relative error bound.
* `IsCoercive.eventually_sqrt_apply_apply_bounds`: uniform comparison of diagonal square roots.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Claim 7.22 and Corollary 7.24.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter
open scoped Topology

/-- A relative error controlled by both squared multiplicative margins bounds the square root. -/
theorem Real.sqrt_bounds_of_abs_sub_sq_le {a x r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (herror : |x - a ^ 2| ≤ min (r ^ 2 - 1) (1 - (r⁻¹) ^ 2) * a ^ 2) :
    a / r ≤ Real.sqrt x ∧ Real.sqrt x ≤ r * a := by
  have hupper : x ≤ (r * a) ^ 2 := by
    have hdu := mul_le_mul_of_nonneg_right (min_le_left (r ^ 2 - 1)
      (1 - (r⁻¹) ^ 2)) (sq_nonneg a)
    have he := (abs_le.mp herror).2
    nlinarith
  have hlower : (a / r) ^ 2 ≤ x := by
    have hdl := mul_le_mul_of_nonneg_right (min_le_right (r ^ 2 - 1)
      (1 - (r⁻¹) ^ 2)) (sq_nonneg a)
    have he := (abs_le.mp herror).1
    rw [div_eq_mul_inv]
    nlinarith
  have hnonneg : 0 ≤ x := (sq_nonneg _).trans hlower
  refine ⟨?_, Real.sqrt_le_iff.mpr ⟨mul_nonneg hr.le ha, hupper⟩⟩
  have hsqrt := Real.sq_sqrt hnonneg
  have hdiv : 0 ≤ a / r := div_nonneg ha hr.le
  nlinarith only [hsqrt, hdiv, hlower, Real.sqrt_nonneg x]

namespace IsCoercive

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- Operator-norm convergence to a coercive form gives uniform multiplicative bounds on the
square roots of diagonal values. No symmetry or positivity assumption on the varying forms
is required. -/
theorem eventually_sqrt_apply_apply_bounds {ι : Type*} {l : Filter ι}
    {B : ι → X →L[ℝ] X →L[ℝ] ℝ} {B₀ : X →L[ℝ] X →L[ℝ] ℝ}
    (h₀ : IsCoercive B₀) (hB : Tendsto B l (𝓝 B₀)) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ s in l, ∀ v : X,
      Real.sqrt (B₀ v v) / r ≤ Real.sqrt (B s v v) ∧
      Real.sqrt (B s v v) ≤ r * Real.sqrt (B₀ v v) := by
  obtain ⟨C, hC, hcoercive⟩ := h₀
  -- Choose an operator-norm error small enough for both multiplicative margins.
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hri1 : r⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr hr
  have hd₁ : 0 < r ^ 2 - 1 := by nlinarith
  have hd₂ : 0 < 1 - (r⁻¹) ^ 2 := by
    have hs := (sq_lt_sq₀ hri.le zero_le_one).mpr hri1
    nlinarith
  let d : ℝ := min (r ^ 2 - 1) (1 - (r⁻¹) ^ 2)
  have hd : 0 < d := lt_min hd₁ hd₂
  have hnear : ∀ᶠ s in l, ‖B s - B₀‖ < d * C := by
    have hb := hB (Metric.ball_mem_nhds B₀ (mul_pos hd hC))
    filter_upwards [hb] with s hs
    simp only [Set.mem_preimage, Metric.mem_ball] at hs
    rwa [dist_eq_norm (B s) B₀] at hs
  filter_upwards [hnear] with s hs
  intro v
  have hnonneg : 0 ≤ B₀ v v :=
    (by positivity : 0 ≤ C * ‖v‖ * ‖v‖).trans (hcoercive v)
  -- Coercivity turns the absolute operator-norm error into relative diagonal error.
  have herror : |B s v v - B₀ v v| ≤ d * B₀ v v := calc
    _ = ‖(B s - B₀) v v‖ := by
      simp only [sub_apply, Real.norm_eq_abs]
    _ ≤ ‖B s - B₀‖ * ‖v‖ * ‖v‖ := (B s - B₀).le_opNorm₂ v v
    _ ≤ (d * C) * ‖v‖ * ‖v‖ := by gcongr
    _ = d * (C * ‖v‖ * ‖v‖) := by ring
    _ ≤ d * B₀ v v := mul_le_mul_of_nonneg_left (hcoercive v) hd.le
  apply Real.sqrt_bounds_of_abs_sub_sq_le (Real.sqrt_nonneg _) hrpos
  simpa only [Real.sq_sqrt hnonneg] using herror

end IsCoercive
