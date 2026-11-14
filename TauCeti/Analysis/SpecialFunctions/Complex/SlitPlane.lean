/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Regularity on the slit plane and the reflected slit domain

Mathlib proves that `Complex.log` is continuous, complex differentiable, and complex analytic at
every point of `Complex.slitPlane = ℂ ∖ (-∞, 0]`. This file establishes the converses, matching
`Real.continuousAt_log_iff` and `Real.differentiableAt_log_iff`: `Complex.log` fails to be
continuous at `0` (where `exp ∘ log` would tend to `1` instead of `0`) and at every negative real
`w < 0` (where the lower half-plane limit has imaginary part `-π` while `log w` has imaginary part
`π`). Consequently, continuity, complex differentiability, and complex analyticity of `Complex.log`
at `z` are all equivalent to `z ∈ Complex.slitPlane`.

It also records the topology and star-convexity at `0` of the reflected slit domain
`{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)`, the principal domain of `-log (1 - z)` and the
polylogarithms.

## Main declarations

* `Complex.continuousAt_log_iff`, `Complex.differentiableAt_log_iff`, `Complex.analyticAt_log_iff`:
  `Complex.log` is continuous, complex differentiable, or complex analytic at `z` if and only if
  `z ∈ Complex.slitPlane`.
* `Complex.isOpen_one_sub_slitPlane`, `Complex.one_sub_ofReal_mul_mem_slitPlane`,
  `Complex.starConvex_zero_one_sub_slitPlane`, `Complex.isPathConnected_one_sub_slitPlane`,
  `Complex.isPreconnected_one_sub_slitPlane`: openness, radial closure, star-convexity at `0`,
  path-connectedness, and preconnectedness of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
-/

public section

open Filter Set Topology

namespace Complex

/-- The reflected slit plane `{z : ℂ | 1 - z ∈ slitPlane} = ℂ ∖ [1, ∞)` is open. -/
theorem isOpen_one_sub_slitPlane : IsOpen {z : ℂ | 1 - z ∈ slitPlane} :=
  isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

/-- If `1 - z ∈ slitPlane` and `t ∈ [0, 1]`, then `1 - t * z ∈ slitPlane`. -/
theorem one_sub_ofReal_mul_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ slitPlane)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 - (t : ℂ) * z ∈ slitPlane := by
  have hz' : 1 + -z ∈ slitPlane := by simpa [sub_eq_add_neg] using hz
  have hmem := starConvex_one_slitPlane.add_smul_mem hz' ht0 ht1
  rwa [real_smul, mul_neg, ← sub_eq_add_neg] at hmem

/-- The reflected slit domain `{z : ℂ | 1 - z ∈ slitPlane}` is star-convex at `0`. -/
theorem starConvex_zero_one_sub_slitPlane : StarConvex ℝ 0 {z : ℂ | 1 - z ∈ slitPlane} := by
  rw [starConvex_zero_iff]
  intro z hz t ht0 ht1
  rw [mem_ofPred_eq, real_smul]
  exact one_sub_ofReal_mul_mem_slitPlane hz ht0 ht1

/-- The reflected slit domain `{z : ℂ | 1 - z ∈ slitPlane}` is path-connected. -/
theorem isPathConnected_one_sub_slitPlane : IsPathConnected {z : ℂ | 1 - z ∈ slitPlane} :=
  starConvex_zero_one_sub_slitPlane.isPathConnected (by simp [one_mem_slitPlane])

/-- The reflected slit domain `{z : ℂ | 1 - z ∈ slitPlane}` is preconnected. -/
theorem isPreconnected_one_sub_slitPlane : IsPreconnected {z : ℂ | 1 - z ∈ slitPlane} :=
  isPathConnected_one_sub_slitPlane.isConnected.isPreconnected

/-- The principal complex logarithm is continuous at `z` if and only if `z ∈ slitPlane`. -/
@[simp]
theorem continuousAt_log_iff {z : ℂ} : ContinuousAt log z ↔ z ∈ slitPlane := by
  refine ⟨fun hcont ↦ by_contra fun hz ↦ ?_, continuousAt_clog⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · have hexp : Tendsto (exp ∘ log) (𝓝[≠] 0) (𝓝 1) := by
      simpa using (continuous_exp.continuousAt.comp hcont).tendsto.mono_left nhdsWithin_le_nhds
    have hid : Tendsto (exp ∘ log) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun u hu ↦ (exp_log hu).symm)
    exact one_ne_zero (tendsto_nhds_unique hexp hid)
  · rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hz
    have hre : z.re < 0 := hz.1.lt_of_ne fun hre0 ↦ hz0 (Complex.ext hre0 hz.2)
    let γ : ℕ → ℂ := fun n ↦ z - (1 / ((n : ℝ) + 1) : ℝ) * I
    have hγ_tendsto : Tendsto γ atTop (𝓝 z) := by
      have hzero : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [γ] using tendsto_const_nhds.sub
        ((continuous_ofReal.continuousAt.tendsto.comp hzero).mul tendsto_const_nhds)
    have hγ_within : Tendsto γ atTop (𝓝[{u : ℂ | u.im < 0}] z) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hγ_tendsto, Eventually.of_forall fun n ↦ ?_⟩
      simp only [mem_ofPred_eq, γ, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one,
        mul_zero, add_zero, hz.2, zero_sub, Right.neg_neg_iff]
      positivity
    have hlim1 : Tendsto (log ∘ γ) atTop (𝓝 (Real.log ‖z‖ - Real.pi * I)) :=
      (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre hz.2).comp hγ_within
    have hlim2 : Tendsto (log ∘ γ) atTop (𝓝 (Real.log ‖z‖ + Real.pi * I)) := by
      have hval : log z = Real.log ‖z‖ + Real.pi * I := by
        rw [log, arg_eq_pi_iff.mpr ⟨hre, hz.2⟩]
      simpa [hval] using hcont.tendsto.comp hγ_tendsto
    have heq := congrArg im (tendsto_nhds_unique hlim1 hlim2)
    simp at heq
    linarith [Real.pi_pos]

/-- The principal complex logarithm is complex differentiable at `z` if and only if
`z ∈ slitPlane`. -/
@[simp]
theorem differentiableAt_log_iff {z : ℂ} : DifferentiableAt ℂ log z ↔ z ∈ slitPlane :=
  ⟨fun hd ↦ continuousAt_log_iff.mp hd.continuousAt, differentiableAt_log⟩

/-- The principal complex logarithm is complex analytic at `z` if and only if `z ∈ slitPlane`. -/
@[simp]
theorem analyticAt_log_iff {z : ℂ} : AnalyticAt ℂ log z ↔ z ∈ slitPlane :=
  ⟨fun ha ↦ continuousAt_log_iff.mp ha.continuousAt, analyticAt_clog⟩

end Complex
