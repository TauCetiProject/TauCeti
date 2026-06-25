/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Bernstein-specific weak limits on `ℝ≥0`

This file contains the Laplace-kernel helper used after Prokhorov extraction in the forward
Bernstein theorem. The generic finite-measure compactness lemma lives in
`TauCeti.MeasureTheory.Measure.Prokhorov`; here the bounded continuous test function is the
specific kernel `p ↦ exp (-x * p)` on `ℝ≥0`.

This implements the Bernstein theorem milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B.

## Main declaration

* `TauCeti.tendsto_exp_integral`: weak convergence of finite measures on `ℝ≥0` implies
  convergence of the corresponding Laplace-kernel integrals.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace TauCeti

/-- The bounded continuous Laplace kernel `p ↦ exp (-x * p)` on `ℝ≥0`, for `x ≥ 0`. -/
private noncomputable def exp_bcf (x : ℝ) (hx : 0 ≤ x) :
    BoundedContinuousFunction ℝ≥0 ℝ where
  toFun p := Real.exp (-(x * (p : ℝ)))
  continuous_toFun := by
    exact (Real.continuous_exp.comp
      ((continuous_const.mul NNReal.continuous_coe).neg))
  map_bounded' := by
    use 2
    intro p q
    simp only [dist_eq_norm, Real.norm_eq_abs]
    have hp : Real.exp (-(x * (p : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx p.2))
    have hq : Real.exp (-(x * (q : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx q.2))
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (-(x * (p : ℝ))),
      Real.exp_pos (-(x * (q : ℝ)))]

/-- Weak convergence of finite measures on `ℝ≥0` implies convergence of the Laplace-kernel
integrals `∫ p, exp (-x * p)`. -/
lemma tendsto_exp_integral
    (σ : ℕ → Measure ℝ≥0) (l : Filter ℕ) (μ₀ : Measure ℝ≥0)
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
      Tendsto (fun n => ∫ p, g p ∂(σ n)) l (nhds (∫ p, g p ∂μ₀)))
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p, Real.exp (-(x * (p : ℝ))) ∂(σ n)) l
      (nhds (∫ p, Real.exp (-(x * (p : ℝ))) ∂μ₀)) := by
  simpa [exp_bcf] using hweak (exp_bcf x hx)

end TauCeti
