/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of dominated iterated derivatives

If the iterated derivatives of a smooth function have integrable envelopes, uniformly on unit
translates, each derivative below the available differentiability order is continuously
differentiable and integrable, and its first derivative has an integrable envelope on unit
translates (`ContDiff.iteratedFDeriv_dominated`). These properties supply the analytic data for
repeated differentiation under the integral sign.
-/

public section

open MeasureTheory

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} {N : ℕ∞} {f : E → F}

/-- If a `C^N` function has integrable envelopes for its iterated derivatives on unit translates,
then each derivative of order `n` with `n + 1 ≤ N` is `C¹` and integrable, and its first derivative
has an integrable envelope on unit translates. -/
theorem ContDiff.iteratedFDeriv_dominated (hf : ContDiff 𝕜 N f)
    (hfφ : ∀ n : ℕ, n ≤ N → ∃ φ : E → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv 𝕜 n f (z + h)‖ ≤ φ z) {n : ℕ} (hn : (n + 1 : ℕ) ≤ N) :
    ContDiff 𝕜 1 (iteratedFDeriv 𝕜 n f) ∧ Integrable (iteratedFDeriv 𝕜 n f) μ ∧
      ∃ φ : E → ℝ, Integrable φ μ ∧
        ∀ z h, ‖h‖ ≤ 1 → ‖fderiv 𝕜 (iteratedFDeriv 𝕜 n f) (z + h)‖ ≤ φ z := by
  have hn' : (n : ℕ∞) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
  obtain ⟨φ₀, hφ₀, hfφ₀⟩ := hfφ n hn'
  obtain ⟨φ₁, hφ₁, hfφ₁⟩ := hfφ (n + 1) hn
  have hfn : ContDiff 𝕜 1 (iteratedFDeriv 𝕜 n f) :=
    hf.iteratedFDeriv_right (by rw [add_comm]; exact_mod_cast hn)
  refine ⟨hfn, hφ₀.mono' hfn.continuous.aestronglyMeasurable (ae_of_all _ fun z => ?_),
    φ₁, hφ₁, fun z h hh => ?_⟩
  · simpa using hfφ₀ z 0 (by simp)
  · rw [norm_fderiv_iteratedFDeriv]
    exact hfφ₁ z h hh
