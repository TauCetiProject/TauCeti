/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrating rank-one operators

A square-integrable vector field gives an integrable operator field by taking its rank-one
operator pointwise. Its integrated matrix coefficients are the integrals of the products of
vector coefficients.
-/

public section

open InnerProductSpace

namespace MeasureTheory.MemLp

variable {𝕜 X V : Type*} [RCLike 𝕜] [MeasurableSpace X] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] {μ : Measure X} {F : X → V}

/-- The rank-one operator of a square-integrable vector field is integrable. -/
theorem integrable_rankOne_self (hF : MemLp F 2 μ) :
    Integrable (fun x ↦ rankOne 𝕜 (F x) (F x)) μ := by
  have hc : Continuous (fun v : V ↦ rankOne 𝕜 v v) := by
    simp only [rankOne_def]
    exact ((StrongDual.smulRightL 𝕜 V V).continuous.comp (innerSL 𝕜).continuous).clm_apply
      continuous_id
  refine (integrable_norm_iff (hc.comp_aestronglyMeasurable hF.aestronglyMeasurable)).mp ?_
  simpa [pow_two] using hF.integrable_norm_pow (p := 2) (by decide)

/-- Matrix coefficients of the integral of rank-one operators are the integrated products of
vector coefficients. The inner product is conjugate-linear in its first argument. -/
theorem inner_integral_rankOne_self [NormedSpace ℝ V] [CompleteSpace V]
    (hF : MemLp F 2 μ) (v w : V) :
    ⟪v, (∫ x, rankOne 𝕜 (F x) (F x) ∂μ) w⟫_𝕜 = ∫ x, ⟪v, F x⟫_𝕜 * ⟪F x, w⟫_𝕜 ∂μ := by
  have hR := hF.integrable_rankOne_self (𝕜 := 𝕜)
  rw [ContinuousLinearMap.integral_apply hR, ← integral_inner (hR.apply_continuousLinearMap w) v]
  simp only [rankOne_apply, inner_smul_right, mul_comm]

end MeasureTheory.MemLp
