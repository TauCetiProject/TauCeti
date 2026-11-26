/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals against a measure with a density in a chart

Let `e` be a chart of a space `M`, with values in a space `E` carrying a measure `ν`, and let a
measure `μ` on `M` have the density `ρ` in `e`: `∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dν(y)` for
continuous compactly supported functions `f` supported in the chart source. This file integrates a
kernel read in the chart against `μ`.

## Main results

* `TauCeti.integral_mul_eq_setIntegral_target`: if `K(x, y) = F(e x, e y)` on the product of the
  chart sources, `K` vanishes elsewhere, and `F(z, w)` vanishes for `w` outside a compact subset of
  the chart target, then `∫ K(x, y) u(y) dμ(y) = ∫_{e.target} ρ(w) F(e x, w) u(e⁻¹ w) dν(w)`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {M E : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M] {μ : Measure M}
  [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {ν : Measure E}
  {e : OpenPartialHomeomorph M E}

/-- **A kernel read in a chart.** Let `μ` have the density `ρ` in the chart `e`, and let `K` be a
continuous function on `M × M` equal to `F (e x, e y)` on the product of the chart sources and to
`0` elsewhere, where `F (z, w)` vanishes for `w` outside a compact subset of the chart target. Then
`∫ K(x, y) u(y) dμ(y) = ∫_{e.target} ρ(w) F(e x, w) u(e⁻¹ w) dν(w)` at points `x` of the chart
source. -/
theorem integral_mul_eq_setIntegral_target {ρ : E → ℝ}
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y) ∂ν)
    {K : M × M → ℂ} (hK : Continuous K) {F : E × E → ℂ}
    (hKF : ∀ p ∈ e.source ×ˢ e.source, K p = F (e p.1, e p.2))
    (hK0 : ∀ p ∉ e.source ×ˢ e.source, K p = 0) {B : Set E} (hB : IsCompact B)
    (hBt : B ⊆ e.target) (hFB : ∀ z, ∀ w ∉ B, F (z, w) = 0) {u : M → ℂ} (hu : Continuous u)
    {x : M} (hx : x ∈ e.source) :
    ∫ y, K (x, y) * u y ∂μ = ∫ w in e.target, (ρ w : ℂ) * F (e x, w) * u (e.symm w) ∂ν := by
  -- The integrand vanishes off the compact set `e⁻¹(B)` inside the chart source.
  have hB' : IsCompact (e.symm '' B) := hB.image_of_continuousOn (e.continuousOn_symm.mono hBt)
  have hfB : ∀ y ∉ e.symm '' B, K (x, y) * u y = 0 := fun y hy ↦ by
    by_cases hys : y ∈ e.source
    · rw [hKF (x, y) ⟨hx, hys⟩, hFB _ _ fun h ↦ hy ⟨_, h, e.left_inv hys⟩, zero_mul]
    · rw [hK0 (x, y) fun h ↦ hys h.2, zero_mul]
  rw [hint (fun y ↦ K (x, y) * u y) ((hK.comp (continuous_const.prodMk continuous_id)).mul hu)
    (HasCompactSupport.intro hB' hfB) ((closure_minimal (Function.support_subset_iff'.2 hfB)
      hB'.isClosed).trans (image_subset_iff.2 fun w hw ↦ e.map_target (hBt hw)))]
  refine setIntegral_congr_fun e.open_target.measurableSet fun w hw ↦ ?_
  simp only [hKF (x, e.symm w) ⟨hx, e.map_target hw⟩, e.right_inv hw, mul_assoc]

end TauCeti
