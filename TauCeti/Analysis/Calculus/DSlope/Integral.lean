/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `dslope` as a parameter integral

For `f : 𝕜 → E` continuously differentiable on an open set containing the segment `[c, w]`
(over `𝕜 = ℝ` or `ℂ`), the divided slope `dslope f c w` is a fundamental-theorem-of-calculus
average of the derivative of `f` along that segment:

  `dslope f c w = ∫ t in 0..1, deriv f (c + t • (w - c))`.

The representation unifies the two branches of `dslope` (`deriv f c` at `c = w`, the slope
`(w - c)⁻¹ • (f w - f c)` otherwise) into a single integral.

## Main results

* `TauCeti.dslope_eq_integral_deriv` — the integral representation.

## Provenance

Adapted from `DslopeIntegral.lean` in the AINTLIB `LeanModularForms` development.
-/

public section

namespace TauCeti

open Set intervalIntegral

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {f : 𝕜 → E}

/-- **The `dslope` integral representation.** When `f` is continuously differentiable on an open
set `U` containing the segment `[c, w]`, `dslope f c w` equals the integral of the derivative of `f`
along the segment. -/
theorem dslope_eq_integral_deriv {U : Set 𝕜} (hU : IsOpen U) (hf : ContDiffOn 𝕜 1 f U) {c w : 𝕜}
    (hcw : segment ℝ c w ⊆ U) :
    dslope f c w = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) := by
  have h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ U := fun t ht ↦
    hcw (segment_eq_image' ℝ c w ▸ mem_image_of_mem _ ht)
  have h_int := integral_unitInterval_deriv_eq_sub
    ((hf.continuousOn_deriv_of_isOpen hU le_rfl).comp (by fun_prop) h_seg) fun t ht ↦
      ((hf.contDiffAt (hU.mem_nhds (h_seg t ht))).differentiableAt one_ne_zero).hasDerivAt
  rw [add_sub_cancel] at h_int
  rcases eq_or_ne w c with rfl | hwc
  · simp
  · rw [dslope_of_ne f hwc, slope_def_module, ← h_int, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.2 hwc), one_smul]

end TauCeti
