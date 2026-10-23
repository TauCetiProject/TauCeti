/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Maps of the line whose increments are dominated by a density

A map `g` defined on a set `s ⊆ ℝ` is said here to have its **increments dominated** by a density
`φ : ℝ → ℝ≥0∞` when

> `edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t` for all `x ≤ y` in `s`.

This is the conclusion the fundamental theorem of calculus delivers for a `C¹` map, with
`φ = ‖deriv g‖ₑ`; it is also the conclusion the chord bound of the length–area method delivers for
a holomorphic map restricted to a circular arc, with `φ` the angular length density
(`TauCeti.ofReal_dist_le_mul_lintegral_Ioc` in `Analysis/Complex/Conformal/LengthArea.lean`). This
file records three consequences of the domination on an order-connected `s`:

* With no finiteness assumption, `Metric.ediam (g '' s) ≤ ∫⁻ t in s, φ t`.
* If the total integral is finite and the target is a pseudo-metric space, `g '' s` is bounded.
* If the total integral is finite, `g` is uniformly continuous on `s`, even for a pseudo-emetric
  target.

Uniform continuity does not follow from bounded variation: domination by a *finite* integral is an
absolute-continuity statement. The set `s` need only be order-connected, so a half-line and the
whole line are covered along with `Ioo a b`, and `φ` need not be measurable, the integrals being
lower integrals throughout.

Uniform continuity is what a boundary-limit argument spends: on a complete target it turns the
Cauchy criterion at an endpoint of `s` into an honest limit there, so a map dominated by a density
of finite integral over `Ioo a b`, where `a < b`, extends continuously to `Icc a b`. The results
are therefore stated in the packaged `UniformContinuousOn` / `Metric.ediam` vocabulary rather than
in `ε`–`δ` form; `EMetric.uniformContinuousOn_iff_le` (or `Metric.uniformContinuousOn_iff_le`)
unpacks the first for a consumer that wants an explicit modulus, and
`Metric.isBounded_iff_ediam_ne_top` the second.

The diameter and boundedness bounds are stated for any measure on a linear order. The diameter
bound allows a weak pseudo-emetric target, and boundedness a pseudo-metric target. Uniform
continuity uses Lebesgue measure on `ℝ` and a pseudo-emetric target.

## Main results

* `Set.OrdConnected.ediam_image_le_of_edist_le_setLIntegral`: the image of an order-connected
  `s` under a map whose increments are dominated by `φ` has diameter at most `∫⁻ t in s, φ t`.
* `Set.OrdConnected.uniformContinuousOn_of_edist_le_setLIntegral`: such a map is uniformly
  continuous on `s` as soon as the total integral is finite.
* `Set.OrdConnected.isBounded_image_of_edist_le_setLIntegral`: for a pseudo-metric target,
  the image is bounded as soon as the total integral is finite.
-/

public section

namespace Set.OrdConnected

open MeasureTheory Set
open scoped ENNReal

section WeakEMetric

variable {α X : Type*} [LinearOrder α] [MeasurableSpace α] {μ : Measure α}
  [TopologicalSpace X] [WeakPseudoEMetricSpace X] {g : α → X} {φ : α → ℝ≥0∞} {s : Set α}

/-- A map whose increments are dominated by `φ` on an order-connected set has image diameter
at most the total integral of `φ`. This holds for any measure on a linear order and a weak
pseudo-emetric target; neither measurability of `φ` nor finiteness of the integral is required. -/
theorem ediam_image_le_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t ∂μ) :
    Metric.ediam (g '' s) ≤ ∫⁻ t in s, φ t ∂μ := by
  have key : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → edist (g u) (g v) ≤ ∫⁻ t in s, φ t ∂μ :=
    fun u hu v hv huv =>
      (hdom u hu v hv huv).trans
        (lintegral_mono_set (Ioc_subset_Icc_self.trans (hs.out hu hv)))
  refine Metric.ediam_image_le_iff.2 fun x hx y hy => ?_
  rcases le_total x y with hxy | hxy
  · exact key x hx y hy hxy
  · rw [edist_comm]
    exact key y hy x hx hxy

end WeakEMetric

section EMetric

variable {X : Type*} [PseudoEMetricSpace X] {g : ℝ → X} {φ : ℝ → ℝ≥0∞} {s : Set ℝ}

/-- **A map whose increments are dominated by a density of finite integral is uniformly
continuous.** For an order-connected `s ⊆ ℝ` and a map `g` with
`edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t` for every increasing pair in `s`, finiteness of
`∫⁻ t in s, φ t` makes `g` uniformly continuous on `s`.

The modulus is uniform over `s`; in particular it does not degrade as an endpoint of `s` is
approached. Finiteness of the total integral cannot be weakened to local integrability, which gives
continuity but no uniform modulus, nor to bounded variation, which gives neither: a monotone jump
function has bounded variation and is not uniformly continuous. -/
theorem uniformContinuousOn_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t)
    (hfin : (∫⁻ t in s, φ t) ≠ ⊤) :
    UniformContinuousOn g s := by
  rw [EMetric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδlt⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (μ := volume.restrict s) (f := φ) hfin hε.ne'
  -- the estimate for a pair in increasing order
  have key : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist x y < δ → edist (g x) (g y) < ε := by
    intro x hx y hy hxy hgap
    have hsub : Ioc x y ⊆ s := Ioc_subset_Icc_self.trans (hs.out hx hy)
    have hmeas : (volume.restrict s) (Ioc x y) < δ := by
      refine (Measure.restrict_apply_le _ _).trans_lt ?_
      simpa [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy)] using hgap
    have hlt := hδlt (Ioc x y) hmeas
    rw [Measure.restrict_restrict_of_subset hsub] at hlt
    exact (hdom x hx y hy hxy).trans_lt hlt
  refine ⟨δ, hδ, fun {x} hx {y} hy hxy => ?_⟩
  rcases le_total x y with hle | hle
  · exact key x hx y hy hle hxy
  · rw [edist_comm] at hxy ⊢
    exact key y hy x hx hle hxy

end EMetric

variable {α X : Type*} [LinearOrder α] [MeasurableSpace α] {μ : Measure α}
  [PseudoMetricSpace X] {g : α → X} {φ : α → ℝ≥0∞} {s : Set α}

/-- **A map whose increments are dominated by a density of finite integral has bounded image.**
The finiteness form of `Set.OrdConnected.ediam_image_le_of_edist_le_setLIntegral`, for a
pseudo-metric target. -/
theorem isBounded_image_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t ∂μ)
    (hfin : (∫⁻ t in s, φ t ∂μ) ≠ ⊤) :
    Bornology.IsBounded (g '' s) :=
  Metric.isBounded_iff_ediam_ne_top.2
    (ne_top_of_le_ne_top hfin (ediam_image_le_of_edist_le_setLIntegral hs hdom))

end Set.OrdConnected
