/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The integral of a compactly supported Laplacian

The Laplacian of a compactly supported twice continuously differentiable function has integral
zero. This is the boundary-free integration identity used in integrated Bochner estimates.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F}

/-- The integral of the Laplacian of a compactly supported `C²` function vanishes. -/
theorem integral_laplacian_eq_zero_of_hasCompactSupport (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ∫ x, Δ f x ∂μ = 0 := by
  let b := stdOrthonormalBasis ℝ E
  have hd := hf.fderiv_right (m := 1) (by norm_num)
  have hi (i) : Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i)) μ :=
    (((hd.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) (b i)).fderiv_apply (𝕜 := ℝ) (b i))
  simp_rw [laplacian_eq_sum_fderiv_fderiv_apply b (hd.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  apply Finset.sum_eq_zero
  intro i _
  exact integral_fderiv_apply_eq_zero_of_hasCompactSupport
    (hd.clm_apply contDiff_const) (hc.fderiv_apply (𝕜 := ℝ) (b i)) (b i)

end TauCeti
