/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Iterated derivatives under a dominated Bochner integral

Mathlib's `hasFTaylorSeriesUpToOn_integral_of_le_bound` differentiates a parametric Bochner
integral `x ↦ ∫ a, f a x ∂μ` on an open set `s` when almost every slice `f a` is given with an
explicit formal Taylor series. When `s` is open, `ContDiffOn 𝕜 n (f a) s` already supplies the
canonical Taylor series `k ↦ iteratedFDeriv 𝕜 k (f a) x`, because derivatives within `s` agree with
unrestricted derivatives (`iteratedFDerivWithin_of_isOpen`).

This file packages the resulting open-set Taylor series differentiation theorem:

* `IsOpen.hasFTaylorSeriesUpToOn_integral_of_dominated`: on an open set `s`, dominated `C^n` slices
  (`n : ℕ∞ω`) integrate to a function whose formal Taylor series is the integral of the slice jets.

No completeness assumption on the target space or topological structure on the measure space is
needed. Because `∫ a in t, f a x ∂μ` is definitionally `∫ a, f a x ∂(μ.restrict t)`, this result
applies directly to set integrals.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace IsOpen

/-- **Formal Taylor series of a dominated Bochner integral.** Let `s ⊆ E` be open and let `f a` be
`C^n` on `s` (`n : ℕ∞ω`) for almost every `a`. If each spatial jet `a ↦ D^k (f a) x` (`k ≤ n`,
`x ∈ s`) is a.e. strongly measurable and dominated uniformly on `s` by an integrable function
`bound k`, then `x ↦ ∫ a, f a x ∂μ` has the integrated spatial jets as its Taylor series up to
order `n` on `s`. -/
theorem hasFTaylorSeriesUpToOn_integral_of_dominated {n : ℕ∞ω} {f : α → E → F} {s : Set E}
    {bound : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ᵐ a ∂μ, ContDiffOn 𝕜 n (f a) s)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a, f a x ∂μ)
      (fun x k ↦ ∫ a, iteratedFDeriv 𝕜 k (f a) x ∂μ) s := by
  refine hasFTaylorSeriesUpToOn_integral_of_le_bound (n := n) (F := fun x a ↦ f a x)
    (p := fun x a k ↦ iteratedFDeriv 𝕜 k (f a) x) (bound := bound) hs hmeas hbound hint ?_
  filter_upwards [hf] with a ha
  exact (ha.ftaylorSeriesWithin hs.uniqueDiffOn).congr_series
    fun k _ x hx ↦ iteratedFDerivWithin_of_isOpen k hs hx

end IsOpen
