/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.TangentSpace
import TauCeti.Analysis.Sobolev.D1p0.Restriction

/-!
# Limits of test gradients in `D^{1,2}_0(E)`

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. The
closure in `L²(μ; E)` of the gradients of test functions (`TauCeti.wassersteinTangentSpace`) and
the homogeneous Sobolev space `D^{1,2}_0(E)` (`TauCeti.D1p0`) are both closures of the test
gradients, the second inside `L²(μ.restrict ⊤; E)`. This file records the resulting inclusion and
its consequence that every limit of test gradients is the weak gradient of a function on the
whole space.

## Main declarations

* `TauCeti.wassersteinTangentSpace_le_comap_d1p0Submodule`: the limits of test gradients lie in
  `D^{1,2}_0(E)`.
* `TauCeti.exists_hasWeakFDerivOn_of_mem_wassersteinTangentSpace`: every limit of test gradients
  is the weak gradient on the whole space of a function `q : E → ℝ`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace InnerProductSpace
open scoped ENNReal Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

variable (μ) in
/-- **Limits of test gradients lie in `D^{1,2}_0(E)`.** Moved to `L²(μ.restrict ⊤; E)`, where the
homogeneous Sobolev space `D^{1,2}_0(E)` lives, the closure in `L²(μ; E)` of the test gradients
lands in `D^{1,2}_0(E)`. -/
theorem wassersteinTangentSpace_le_comap_d1p0Submodule :
    wassersteinTangentSpace μ ≤ (d1p0Submodule μ ⊤ 2).toSubmodule.comap
      (LpToLpRestrictCLM E E ℝ μ 2 ((⊤ : Opens E) : Set E)).toLinearMap := by
  set ρ := LpToLpRestrictCLM E E ℝ μ 2 ((⊤ : Opens E) : Set E)
  refine (wassersteinTangentSpace_le_iff ((d1p0Submodule μ ⊤ 2).isClosed.preimage
    ρ.continuous)).2 fun φ hφ hφc f hf ↦ ?_
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hφc, by simp⟩
  have heq : ρ f = D1p0.ofTestFunctionₗ μ ⊤ 2 ψ := by
    rw [D1p0.coe_ofTestFunctionₗ]
    refine Lp.ext ?_
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ _ f, ae_restrict_of_ae hf,
      gradientTestFunctionLp_apply_ae 2 ψ] with x h₁ h₂ h₃
    simp only [ρ, ψ, h₁, h₂, h₃, TestFunction.coe_mk]
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, heq]
  exact (D1p0.ofTestFunctionₗ μ ⊤ 2 ψ).property

/-- **Limits of test gradients are weak gradients.** Every element of the closure in `L²(μ; E)`
of the test gradients is the weak gradient on the whole space of a function `q : E → ℝ`. -/
theorem exists_hasWeakFDerivOn_of_mem_wassersteinTangentSpace {w : Lp E 2 μ}
    (hw : w ∈ wassersteinTangentSpace μ) :
    ∃ q : E → ℝ, HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x) := by
  obtain ⟨q, hq⟩ := D1p0.exists_hasWeakFDerivOn
    (⟨_, wassersteinTangentSpace_le_comap_d1p0Submodule μ hw⟩ : D1p0 μ ⊤ 2)
  refine ⟨q, hq.congr_ae_deriv ?_⟩
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ _ w] with x hx
  simp only [ContinuousLinearMap.coe_coe, hx]

end TauCeti
