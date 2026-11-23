/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Inner products of interval integrals

For interval-integrable functions `f` and `g` taking values in a Hilbert space over `𝕜`
(`RCLike 𝕜`), the inner product of their interval integrals is the double interval integral of
their pointwise inner products:

`⟪∫ s in a..b, f s ∂μ, ∫ t in c..d, g t ∂ν⟫_𝕜 = ∫ s in a..b, ∫ t in c..d, ⟪f s, g t⟫_𝕜 ∂ν ∂μ`.

Specializing to `f = g` expresses the squared norm of an interval integral as the double interval
integral of `⟪f s, f t⟫_𝕜`.

## Main results

* `TauCeti.inner_intervalIntegral_eq`: the inner product of two interval integrals is the double
  interval integral of the pointwise inner products.
* `TauCeti.norm_intervalIntegral_sq_eq`: the squared norm of an interval integral as a double
  interval integral of inner products.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

/-- The inner product of two interval integrals is the double interval integral of the pointwise
inner products. -/
theorem inner_intervalIntegral_eq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] {μ ν : Measure ℝ}
    {f g : ℝ → E} {a b c d : ℝ}
    (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g ν c d) :
    ⟪∫ s in a..b, f s ∂μ, ∫ t in c..d, g t ∂ν⟫_𝕜 =
      ∫ s in a..b, ∫ t in c..d, ⟪f s, g t⟫_𝕜 ∂ν ∂μ := by
  calc
    ⟪∫ s in a..b, f s ∂μ, ∫ t in c..d, g t ∂ν⟫_𝕜
        = ∫ s in a..b, ⟪f s, ∫ t in c..d, g t ∂ν⟫_𝕜 ∂μ := by
      have hcomm := (innerSL 𝕜 (∫ t in c..d, g t ∂ν)).intervalIntegral_comp_comm hf
      simp only [innerSL_apply_apply] at hcomm
      rw [← inner_conj_symm, ← hcomm, ← _root_.intervalIntegral.intervalIntegral_conj]
      simp_rw [inner_conj_symm]
    _ = ∫ s in a..b, ∫ t in c..d, ⟪f s, g t⟫_𝕜 ∂ν ∂μ :=
      _root_.intervalIntegral.integral_congr fun s _ =>
        ((innerSL 𝕜 (f s)).intervalIntegral_comp_comm hg).symm

/-- The squared norm of an interval integral (embedded in `𝕜`) as the double interval integral of
the pointwise inner products `⟪f s, f t⟫_𝕜`. -/
theorem norm_intervalIntegral_sq_eq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure ℝ}
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f μ a b) :
    ((‖∫ t in a..b, f t ∂μ‖ ^ 2 : ℝ) : 𝕜) = ∫ s in a..b, ∫ t in a..b, ⟪f s, f t⟫_𝕜 ∂μ ∂μ := by
  simpa only [RCLike.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (∫ t in a..b, f t ∂μ)).symm.trans
      (inner_intervalIntegral_eq hf hf)

end TauCeti
