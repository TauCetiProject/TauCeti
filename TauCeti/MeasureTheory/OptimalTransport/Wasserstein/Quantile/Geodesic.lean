/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Isometry
import TauCeti.MeasureTheory.Function.Lp.StrictConvex

/-!
# The geodesics of the one-dimensional Wasserstein space

For every exponent `1 ≤ p ≤ ∞`, quantile interpolation is a geodesic segment of `P_p(ℝ)`: the law
whose quantile function is `(1 - s) Q₀ + s Q₁` runs at constant speed from `μ₀` to `μ₁`
(`TauCeti.exists_isGeodesicSegment_quantileBarycenter`). This file proves that for `1 < p < ∞` it
is the only one. The quantile map is an isometry of `P_p(ℝ)` into `Lᵖ(0, 1)`
(`TauCeti.WassersteinSpace.isometry_quantileLp`), the space `Lᵖ(0, 1)` is strictly convex
(`MeasureTheory.Lp.strictConvexSpace`), and the only geodesic segment of a strictly convex normed
space is the affine one (`TauCeti.IsGeodesicSegment.eq_lineMap`). So the quantile function of the
point at time `s` of every geodesic segment is `(1 - s) Q₀ + s Q₁`, and `P_p(ℝ)` is uniquely
geodesic.

Neither endpoint exponent is uniquely geodesic. At `p = 1` the mixtures `(1 - s) δ₀ + s δ₁` and
the translates `δ_s` both form geodesic segments from `δ₀` to `δ₁`. That is why the strict
convexity of `Lᵖ(0, 1)`, rather than the isometry alone, carries the uniqueness.

## Main statements

* `TauCeti.WassersteinSpace.quantileLp_apply_eq_lineMap` — along a geodesic segment of `P_p(ℝ)`,
  the quantile function moves affinely in `Lᵖ(0, 1)`.
* `TauCeti.WassersteinSpace.eqOn_of_isGeodesicSegment` — `P_p(ℝ)` is uniquely geodesic.
* `TauCeti.WassersteinSpace.isGeodesicSegment_iff_coe_eq_quantileBarycenter` — a curve is a
  geodesic segment of `P_p(ℝ)` exactly when it is the quantile interpolation on `[0, 1]`.

## References

* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2 and
  §5.4, for the quantile description of one-dimensional transport and Wasserstein geodesics.
* B. Kloeckner, *A geometric study of Wasserstein spaces: Euclidean spaces*, Ann. Sc. Norm.
  Super. Pisa Cl. Sci. (5) 9 (2010), 297--323, where `P₂(ℝ)` is identified with a convex subset of
  `L²(0, 1)`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace WassersteinSpace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {γ γ' : ℝ → WassersteinSpace p ℝ}
  {μ₀ μ₁ : WassersteinSpace p ℝ}

/-- **Quantile functions move affinely along Wasserstein geodesics.** For `1 < p < ∞`, if `γ` is a
geodesic segment of `P_p(ℝ)` from `μ₀` to `μ₁`, then for every `s ∈ [0, 1]` the quantile function
of `γ s` is, as an element of `Lᵖ(0, 1)`, the affine combination `(1 - s) Q₀ + s Q₁`. -/
theorem quantileLp_apply_eq_lineMap (hp : 1 < p) (hp_top : p ≠ ∞)
    (h : IsGeodesicSegment γ μ₀ μ₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    quantileLp (γ s) = AffineMap.lineMap (quantileLp μ₀) (quantileLp μ₁) s := by
  have := Lp.strictConvexSpace (E := ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1)) hp hp_top
  exact (h.comp_isometry isometry_quantileLp).eq_lineMap hs

/-- **`P_p(ℝ)` is uniquely geodesic.** For `1 < p < ∞`, two geodesic segments of `P_p(ℝ)` with the
same endpoints agree on `[0, 1]`. This fails at `p = 1`. -/
theorem eqOn_of_isGeodesicSegment (hp : 1 < p) (hp_top : p ≠ ∞)
    (h : IsGeodesicSegment γ μ₀ μ₁) (h' : IsGeodesicSegment γ' μ₀ μ₁) : EqOn γ γ' (Icc 0 1) := by
  have := Lp.strictConvexSpace (E := ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1)) hp hp_top
  exact IsGeodesicSegment.eqOn_of_isometry isometry_quantileLp h h'

/-- **The geodesics of `P_p(ℝ)` are the quantile interpolations.** For `1 < p < ∞`, a curve `γ` is
a geodesic segment of `P_p(ℝ)` from `μ₀` to `μ₁` exactly when, for every `s ∈ [0, 1]`, the law
`γ s` is the quantile interpolation of `μ₀` and `μ₁` at time `s`, whose quantile function is
`(1 - s) Q₀ + s Q₁`. -/
theorem isGeodesicSegment_iff_coe_eq_quantileBarycenter (hp : 1 < p) (hp_top : p ≠ ∞) :
    IsGeodesicSegment γ μ₀ μ₁ ↔ ∀ s ∈ Icc (0 : ℝ) 1,
      ((γ s : ProbabilityMeasure ℝ) : Measure ℝ) =
        quantileBarycenter ![(1 - s).toNNReal, s.toNNReal]
          ![((μ₀ : ProbabilityMeasure ℝ) : Measure ℝ),
            ((μ₁ : ProbabilityMeasure ℝ) : Measure ℝ)] := by
  obtain ⟨γ₀, hγ₀, hβ⟩ := exists_isGeodesicSegment_quantileBarycenter μ₀ μ₁
  refine ⟨fun h s hs ↦ ?_, fun hγ ↦ hγ₀.congr fun s hs ↦ ?_⟩
  · rw [eqOn_of_isGeodesicSegment hp hp_top h hγ₀ hs, hβ s hs]
  · exact ext (ProbabilityMeasure.toMeasure_injective ((hγ s hs).trans (hβ s hs).symm))

end WassersteinSpace

end TauCeti
