/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Test functions as continuous functions vanishing at infinity

A test function has compact support, so it vanishes at infinity. This file bundles the inclusion
of `𝓓^{n}(Ω, F)` into the space `C₀(E, F)` of continuous functions vanishing at infinity as a
continuous linear map. It is the `C₀` counterpart of Mathlib's
`TestFunction.toBoundedContinuousFunctionCLM`, through which its continuity is proved.

## Main declarations

* `TestFunction.toZeroAtInftyCLM`: the inclusion `𝓓^{n}(Ω, F) →L[𝕜] C₀(E, F)`.
-/

public section

namespace TestFunction

open TopologicalSpace
open scoped Distributions ZeroAtInfty

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] {n : ℕ∞}

variable (𝕜) in
/-- The inclusion of the space `𝓓^{n}(Ω, F)` into the space `C₀(E, F)` of continuous functions
vanishing at infinity, as a continuous `𝕜`-linear map. -/
noncomputable def toZeroAtInftyCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] :
    𝓓^{n}(Ω, F) →L[𝕜] C₀(E, F) :=
  TestFunction.mkCLM 𝕜 (fun f => ⟨⟨f, f.continuous⟩, f.hasCompactSupport.is_zero_at_infty⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ K_sub_Ω =>
      -- `C₀(E, F)` carries the metric induced from `E →ᵇ F`.
      ZeroAtInftyContinuousMap.isometry_toBCF.isUniformInducing.isInducing.continuous_iff.2
        ((toBoundedContinuousFunctionCLM 𝕜).continuous.comp (continuous_ofSupportedIn K_sub_Ω))

/-- The inclusion into `C₀(E, F)` does not change the underlying function. -/
@[simp]
theorem coe_toZeroAtInftyCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) :
    ⇑(toZeroAtInftyCLM 𝕜 f) = f :=
  (rfl)

end TestFunction
