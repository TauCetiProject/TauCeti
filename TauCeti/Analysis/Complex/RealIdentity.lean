/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Entire functions are determined by their values on the real line

Two entire functions with values in a complex Banach space that agree at every real point are
equal. This is the identity principle `AnalyticOnNhd.eq_of_frequently_eq`, applied at the
accumulation point `0` of the real axis. It is the uniqueness statement behind analytic
continuation of real one-parameter orbits to complex time.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Two entire functions agreeing on the real line are equal. -/
theorem Differentiable.eq_of_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ t : ℝ, f t = g t) : f = g := by
  have hmaps : Set.MapsTo ((↑) : ℝ → ℂ) {0}ᶜ {0}ᶜ := fun t ht => by
    simpa using ht
  have htendsto : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa using Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (x := (0 : ℝ)) hmaps
  exact AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hf.analyticAt z)
    (fun z _ => hg.analyticAt z) (htendsto.frequently (Frequently.of_forall h))
