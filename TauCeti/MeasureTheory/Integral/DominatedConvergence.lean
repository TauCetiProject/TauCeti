/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence away from one point

This file packages the common application of dominated convergence in which a continuously
parameterized family is controlled and converges pointwise away from one exceptional point. When
singletons have measure zero, the pointwise hypotheses supply the almost-everywhere hypotheses of
the dominated convergence theorem.

## Main declarations

* `TauCeti.tendsto_integral_mul_of_dominated_away`: dominated convergence for a family multiplied
  by a fixed continuous weight, with domination and convergence away from one point.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology

variable {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [NullSingletonClass μ] {l : Filter ι} [l.IsCountablyGenerated]

/-- **Dominated convergence away from one point.** Suppose `K i` is eventually continuous, `w`
is continuous, and `K i` is eventually dominated by `K₀` and converges to it away from a point
`x₀`. If `K₀ * w` is integrable and singletons are null, then the integrals of `K i * w` converge
to the integral of `K₀ * w`.

The exceptional point is useful for regularizations of singular kernels. The statement is for an
arbitrary countably generated filter and an arbitrary measured topological space.
-/
theorem tendsto_integral_mul_of_dominated_away (x₀ : α) {K : ι → α → ℝ} {K₀ w : α → ℝ}
    (hw : Continuous w) (hK : ∀ᶠ i in l, Continuous (K i))
    (hint : Integrable (fun x ↦ K₀ x * w x) μ)
    (hle : ∀ᶠ i in l, ∀ x ≠ x₀, |K i x| ≤ |K₀ x|)
    (hlim : ∀ x ≠ x₀, Tendsto (fun i ↦ K i x) l (𝓝 (K₀ x))) :
    Tendsto (fun i ↦ ∫ x, K i x * w x ∂μ) l (𝓝 (∫ x, K₀ x * w x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K₀ x * w x‖)
    (hK.mono fun _ hi ↦ (hi.mul hw).aestronglyMeasurable) ?_ hint.norm ?_
  · filter_upwards [hle] with i hi
    filter_upwards [μ.ae_ne x₀] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hi x hx) (abs_nonneg _)
  · filter_upwards [μ.ae_ne x₀] with x hx
    exact (hlim x hx).mul_const _

end TauCeti
