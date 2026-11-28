/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Limits of the logarithm

The logarithmic scale of a fixed nonzero numerator divided by a variable approaching zero
tends to infinity. This supplies the diverging scale in logarithmic cutoff estimates. Conversely, if
`f : ℝ → ℝ` is differentiable at `0`, then `(f x - f 0) * Real.log x → 0` as `x → 0⁺`.

## Main results

* `Real.tendsto_log_div_nhdsNE_zero`: for `δ ≠ 0`, `log (δ / ε) → ∞` as `ε → 0`, `ε ≠ 0`.
* `Real.tendsto_sub_mul_log_nhdsGT_zero`: if `f` is differentiable at `0`, then
  `(f x - f 0) * log x → 0` as `x → 0⁺`.

Adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Tendsto.lean`.
-/

public section

open Filter Set Topology

namespace Real

/-- For fixed `δ ≠ 0`, the scale `log (δ / ε)` tends to infinity as `ε → 0`
through nonzero values. -/
theorem tendsto_log_div_nhdsNE_zero {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun ε ↦ Real.log (δ / ε)) (𝓝[≠] 0) atTop := by
  have h := tendsto_atTop_add_const_left _ (Real.log δ)
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, Real.log_div hδ hε]
  ring

/-- If `f : ℝ → ℝ` is differentiable at `0`, then `(f x - f 0) * log x → 0` as `x → 0⁺`. -/
theorem tendsto_sub_mul_log_nhdsGT_zero {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) :
    Tendsto (fun x : ℝ ↦ (f x - f 0) * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  have hmul := (((hasDerivAt_iff_tendsto_slope.mp hf.hasDerivAt).mono_left
      (nhdsWithin_mono 0 fun _ (hx : _ ∈ Ioi (0 : ℝ)) ↦ hx.ne')).congr
      (f₂ := fun x : ℝ ↦ (f x - f 0) / x) fun _ ↦ by simp [slope_def_field]).mul
    (by simpa using (Real.continuous_mul_log.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto :
      Tendsto (fun x : ℝ ↦ x * Real.log x) (𝓝[>] 0) (𝓝 0))
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  field_simp [hx.ne']

end Real
