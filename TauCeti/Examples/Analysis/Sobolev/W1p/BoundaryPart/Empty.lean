/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Example: no Poincaré–Friedrichs inequality on `W^{1,p}_∅(0, 1)`

With `Γ = ∅`, the restriction to `(0, 1)` of a bump on `ℝ` equal to `1` on `[0, 1]` is a
generator of `W^{1,p}_∅(0, 1)`: a constant with zero weak gradient and nonzero `Lᵖ` norm. So no
inequality `‖u‖_p ≤ C ‖∇u‖_p` holds on `W^{1,p}_∅(0, 1)`.
-/

public section

open MeasureTheory Set TopologicalSpace TauCeti TauCeti.W1p
open scoped Distributions ENNReal Gradient

namespace TauCeti.W1pVanishingOnEmptyExamples

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- With `Γ = ∅`, no inequality `‖u‖_p ≤ C ‖∇u‖_p` holds on `W^{1,p}_∅(0, 1)`. -/
example : ¬∃ C : ℝ, ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p ∅,
    ‖value u‖ ≤ C * ‖gradient u‖ := by
  rintro ⟨C, hC⟩
  -- a bump on `ℝ` equal to `1` on `[0, 1] = closedBall (1/2) (1/2)`
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let φ : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨⇑f, f.contDiff, f.hasCompactSupport, by simp⟩
  have hφ : (⇑φ : ℝ → ℝ) = ⇑f := TestFunction.coe_mk
  have hle : (⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤ := le_top
  set u := restrictL hle (ofTestFunctionₗ volume ⊤ p φ)
  have hone (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : (⇑f : ℝ → ℝ) =ᶠ[nhds x] fun _ ↦ 1 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hval : value u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ ↦ (1 : ℝ) := by
    filter_upwards [value_restrictL_ofTestFunctionₗ_ae (p := p) hle φ,
      ae_restrict_mem measurableSet_Ioo] with x h1 hx
    rw [h1, hφ]
    exact (hone x hx).eq_of_nhds
  have hgrad : gradient u = 0 := by
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [gradient_restrictL_ofTestFunctionₗ_ae (p := p) hle φ,
      ae_restrict_mem measurableSet_Ioo] with x h1 hx
    rw [h1, Pi.zero_apply, hφ, gradient_eq_deriv', (hone x hx).deriv_eq, deriv_const]
  have hu := hC u (restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (by simp))
  rw [hgrad, norm_zero, mul_zero, norm_le_zero_iff] at hu
  have h0 : (fun _ ↦ (1 : ℝ)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 :=
    hval.symm.trans (hu ▸ Lp.coeFn_zero ℝ p _)
  have : (ae (volume.restrict (Ioo (0 : ℝ) 1))).NeBot :=
    ae_neBot.2 (by simp [Measure.restrict_eq_zero])
  obtain ⟨x, hx⟩ := h0.exists
  simp at hx

end TauCeti.W1pVanishingOnEmptyExamples
