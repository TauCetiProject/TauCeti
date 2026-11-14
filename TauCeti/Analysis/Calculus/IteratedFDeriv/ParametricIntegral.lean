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

This file packages the resulting open-set and local-neighbourhood differentiation theorems directly
in terms of `ContDiffOn`, `ContDiffAt`, and `iteratedFDeriv`:

* `TauCeti.hasFTaylorSeriesUpToOn_integral_of_dominated`: on an open set `s`, dominated `C^n`
  slices integrate to a function whose formal Taylor series is the integral of the slice jets.
* `TauCeti.contDiffOn_integral_of_dominated` and
  `TauCeti.iteratedFDeriv_integral_of_dominated_of_isOpen`: `C^n` regularity on `s` and commutation
  of `iteratedFDeriv 𝕜 k` with the Bochner integral for `k ≤ n`.
* `TauCeti.contDiffAt_integral_of_dominated`, `TauCeti.iteratedFDeriv_integral_of_dominated`, and
  `TauCeti.norm_iteratedFDeriv_integral_le_of_dominated`: local forms at a point `x₀` when
  domination holds on a neighbourhood `s ∈ 𝓝 x₀` (such as a closed ball), deduced by restricting to
  `interior s`.

No completeness assumption on the target space or topological structure on the measure space is
needed. Because `∫ a in t, f a x ∂μ` is definitionally `∫ a, f a x ∂(μ.restrict t)`, all results
apply directly to set integrals.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Formal Taylor series of a dominated Bochner integral.** Let `s ⊆ E` be open and let `f a` be
`C^n` on `s` for almost every `a`. If each spatial jet `a ↦ D^k (f a) x` (`k ≤ n`, `x ∈ s`) is
a.e. strongly measurable and dominated uniformly on `s` by an integrable function `bound k`, then
`x ↦ ∫ a, f a x ∂μ` has the integrated spatial jets as its Taylor series up to order `n` on `s`. -/
theorem hasFTaylorSeriesUpToOn_integral_of_dominated {n : ℕ∞} {f : α → E → F} {s : Set E}
    {bound : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ᵐ a ∂μ, ContDiffOn 𝕜 n (f a) s)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a, f a x ∂μ)
      (fun x k ↦ ∫ a, iteratedFDeriv 𝕜 k (f a) x ∂μ) s := by
  refine hasFTaylorSeriesUpToOn_integral_of_le_bound (n := (n : ℕ∞ω)) (F := fun x a ↦ f a x)
    (p := fun x a k ↦ iteratedFDeriv 𝕜 k (f a) x) (bound := bound) hs
    (fun x hx k hk ↦ hmeas x hx k (mod_cast hk))
    (hbound.mono fun a ha x hx k hk ↦ ha x hx k (mod_cast hk))
    (fun k hk ↦ hint k (mod_cast hk)) ?_
  filter_upwards [hf] with a ha
  exact (ha.ftaylorSeriesWithin hs.uniqueDiffOn).congr_series
    fun k _ x hx ↦ iteratedFDerivWithin_of_isOpen k hs hx

/-- **Smoothness of a dominated Bochner integral on an open set.** Under uniform integrable bounds
on the spatial jets up to order `n` on an open set `s`, `x ↦ ∫ a, f a x ∂μ` is `C^n` on `s`. -/
theorem contDiffOn_integral_of_dominated {n : ℕ∞} {f : α → E → F} {s : Set E}
    {bound : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ᵐ a ∂μ, ContDiffOn 𝕜 n (f a) s)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ) :
    ContDiffOn 𝕜 n (fun x ↦ ∫ a, f a x ∂μ) s :=
  (hasFTaylorSeriesUpToOn_integral_of_dominated hs hf hmeas hbound hint).contDiffOn

/-- **Iterated derivatives under a dominated Bochner integral on an open set.** For every `k ≤ n`
and `x ∈ s`, `iteratedFDeriv 𝕜 k` commutes with integration against `μ`. -/
theorem iteratedFDeriv_integral_of_dominated_of_isOpen {n : ℕ∞} {f : α → E → F} {s : Set E}
    {bound : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ᵐ a ∂μ, ContDiffOn 𝕜 n (f a) s)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ)
    {k : ℕ} (hk : k ≤ n) {x : E} (hx : x ∈ s) :
    iteratedFDeriv 𝕜 k (fun y ↦ ∫ a, f a y ∂μ) x =
      ∫ a, iteratedFDeriv 𝕜 k (f a) x ∂μ := by
  have hT := hasFTaylorSeriesUpToOn_integral_of_dominated hs hf hmeas hbound hint
  rw [← iteratedFDerivWithin_of_isOpen k hs hx]
  exact (hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast hk) hs.uniqueDiffOn hx).symm

/-- **Local smoothness of a dominated Bochner integral.** If domination and pointwise `C^n`
regularity of the slices hold on a neighbourhood `s ∈ 𝓝 x₀`, then `x ↦ ∫ a, f a x ∂μ` is `C^n` at
`x₀`. -/
theorem contDiffAt_integral_of_dominated {n : ℕ∞} {f : α → E → F} {s : Set E} {x₀ : E}
    {bound : ℕ → α → ℝ} (hs : s ∈ 𝓝 x₀)
    (hf : ∀ᵐ a ∂μ, ∀ x ∈ s, ContDiffAt 𝕜 n (f a) x)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ) :
    ContDiffAt 𝕜 n (fun x ↦ ∫ a, f a x ∂μ) x₀ := by
  refine (contDiffOn_integral_of_dominated isOpen_interior
    (hf.mono fun _ ha x hx ↦ (ha x (interior_subset hx)).contDiffWithinAt)
    (fun x hx ↦ hmeas x (interior_subset hx))
    (hbound.mono fun _ ha x hx ↦ ha x (interior_subset hx)) hint).contDiffAt ?_
  exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs)

/-- **Iterated derivatives under a locally dominated Bochner integral.** If domination and
pointwise `C^n` regularity of the slices hold on a neighbourhood `s ∈ 𝓝 x₀`, then for every
`k ≤ n` the `k`-th iterated derivative at `x₀` is the integral of the `k`-th slice derivatives. -/
theorem iteratedFDeriv_integral_of_dominated {n : ℕ∞} {f : α → E → F} {s : Set E} {x₀ : E}
    {bound : ℕ → α → ℝ} (hs : s ∈ 𝓝 x₀)
    (hf : ∀ᵐ a ∂μ, ∀ x ∈ s, ContDiffAt 𝕜 n (f a) x)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ)
    {k : ℕ} (hk : k ≤ n) :
    iteratedFDeriv 𝕜 k (fun x ↦ ∫ a, f a x ∂μ) x₀ =
      ∫ a, iteratedFDeriv 𝕜 k (f a) x₀ ∂μ :=
  iteratedFDeriv_integral_of_dominated_of_isOpen isOpen_interior
    (hf.mono fun _ ha x hx ↦ (ha x (interior_subset hx)).contDiffWithinAt)
    (fun x hx ↦ hmeas x (interior_subset hx))
    (hbound.mono fun _ ha x hx ↦ ha x (interior_subset hx)) hint hk
    (mem_interior_iff_mem_nhds.mpr hs)

/-- **Norm bound for iterated derivatives of a locally dominated Bochner integral.** Under the
hypotheses of `iteratedFDeriv_integral_of_dominated`, the norm of the `k`-th iterated derivative at
`x₀` is bounded by the integral of `bound k`. -/
theorem norm_iteratedFDeriv_integral_le_of_dominated {n : ℕ∞} {f : α → E → F} {s : Set E} {x₀ : E}
    {bound : ℕ → α → ℝ} (hs : s ∈ 𝓝 x₀)
    (hf : ∀ᵐ a ∂μ, ∀ x ∈ s, ContDiffAt 𝕜 n (f a) x)
    (hmeas : ∀ x ∈ s, ∀ k : ℕ, k ≤ n →
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv 𝕜 k (f a) x) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv 𝕜 k (f a) x‖ ≤ bound k a)
    (hint : ∀ k : ℕ, k ≤ n → Integrable (bound k) μ)
    {k : ℕ} (hk : k ≤ n) :
    ‖iteratedFDeriv 𝕜 k (fun x ↦ ∫ a, f a x ∂μ) x₀‖ ≤ ∫ a, bound k a ∂μ := by
  rw [iteratedFDeriv_integral_of_dominated hs hf hmeas hbound hint hk]
  exact norm_integral_le_of_norm_le (hint k hk)
    (hbound.mono fun _ ha ↦ ha x₀ (mem_of_mem_nhds hs) k hk)

end TauCeti
