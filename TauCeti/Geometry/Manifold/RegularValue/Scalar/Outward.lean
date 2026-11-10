/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel

/-!
# The outward co-orientation of regular sublevels and bands

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. The sublevel `{f ≤ a}` is a manifold with
boundary for its atlas `TauCeti.scalarRegularSublevelChartedSpace`, with boundary the level
`f⁻¹(a)`. This file shows that `f` itself detects the outward direction: at a point of the level, a
tangent vector `v` of the sublevel points outward (`TauCeti.IsOutwardPointing`) exactly when `f`
increases along it, that is, when the derivative of the restriction of `f` to the sublevel is
positive on `v` (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff`).

For a band `f⁻¹([a, b])` between regular values `a < b`, with atlas
`TauCeti.scalarRegularBandChartedSpace`, the derivative of `f` is negative on outward vectors at the
lower level `f⁻¹(a)` and positive on them at the upper level `f⁻¹(b)`
(`TauCeti.isOutwardPointing_scalarRegularBand_iff_of_eq_left` and
`TauCeti.isOutwardPointing_scalarRegularBand_iff_of_eq_right`).

These co-orientations involve no metric and no orientation of `M`: they are read off from the
sign of the derivative of `f` alone.

The proof reads the derivative in the preferred face charts: there the zeroth coordinate is the
inward coordinate `a - f` of the sublevel, respectively `f - a` and `b - f` at the two faces of the
band, and a vector is outward exactly when the derivative of that coordinate is negative on it
(`TauCeti.isOutwardPointing_iff_mul_mvfderiv_neg`).

## Main results

* `TauCeti.isOutwardPointing_scalarRegularSublevel_iff`: on the boundary of `{f ≤ a}`, outward
  vectors are those on which `df > 0`.
* `TauCeti.isOutwardPointing_scalarRegularBand_iff_of_eq_left`: on the lower face of
  `f⁻¹([a, b])`, outward vectors are those on which `df < 0`.
* `TauCeti.isOutwardPointing_scalarRegularBand_iff_of_eq_right`: on the upper face of
  `f⁻¹([a, b])`, outward vectors are those on which `df > 0`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 5 (boundary defining functions and inward-pointing vectors;
  Proposition 5.47, regular sublevel sets are regular domains).
-/

public section

open Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M] (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hn : finrank ℝ E = n + 1)

/-- **The outward co-orientation of a regular sublevel.** At a point `x` of the level `f⁻¹(a)`, a
tangent vector `v` of the sublevel `{f ≤ a}` points outward exactly when the derivative of `f` is
positive on it. -/
theorem isOutwardPointing_scalarRegularSublevel_iff (hreg : IsRegularValue I 𝓘(ℝ) f a)
    {x : {x | f x ≤ a}} (hx : f x = a)
    (v : letI := scalarRegularSublevelChartedSpace hf hreg hn; TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    IsOutwardPointing x v ↔ 0 < mvfderiv (𝓡∂ (n + 1)) (fun w : {x | f x ≤ a} ↦ f w) x v := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  have hxb : x ∈ (𝓡∂ (n + 1)).boundary {x | f x ≤ a} := by
    rw [boundary_scalarRegularSublevel hreg hn le_rfl hf]
    exact hx
  -- The inward coordinate of the preferred face chart is `a - f`.
  have hchart (w) (hw : w ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
      (chartAt (EuclideanHalfSpace (n + 1)) x w).1 0 = -1 * (f w - a) := by
    rw [scalarRegularSublevelChartedSpace_chartAt] at hw ⊢
    rw [scalarRegularSublevelChartAt_apply_zero_of_eq hf hreg hn hx hw]
    ring
  rw [isOutwardPointing_iff_mul_mvfderiv_neg hxb (by norm_num)
    (Filter.eventually_of_mem (chart_source_mem_nhds _ x) hchart), neg_one_mul, neg_lt_zero]

section Band

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- **The outward co-orientation of a band at its lower level.** At a point `x` of the lower level
`f⁻¹(a)` of a band `f⁻¹([a, b])` between regular values, a tangent vector `v` of the band points
outward exactly when the derivative of `f` is negative on it. -/
theorem isOutwardPointing_scalarRegularBand_iff_of_eq_left {x : f ⁻¹' Icc a b} (hx : f x = a)
    (v : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x v ↔ mvfderiv (𝓡∂ (n + 1)) (fun w : f ⁻¹' Icc a b ↦ f w) x v < 0 := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  have hxb : x ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [boundary_scalarRegularBand hn ha hb le_rfl hf hab]
    exact Or.inl hx
  -- The inward coordinate of the preferred chart at the lower face is `f - a`.
  have hchart (w) (hw : w ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
      (chartAt (EuclideanHalfSpace (n + 1)) x w).1 0 = 1 * (f w - a) := by
    rw [scalarRegularBandChartedSpace_chartAt] at hw ⊢
    rw [scalarRegularBandChartAt_apply_zero_of_eq_left hf hn ha hb hx hw, one_mul]
  rw [isOutwardPointing_iff_mul_mvfderiv_neg hxb one_ne_zero
    (Filter.eventually_of_mem (chart_source_mem_nhds _ x) hchart), one_mul]

/-- **The outward co-orientation of a band at its upper level.** At a point `x` of the upper level
`f⁻¹(b)` of a band `f⁻¹([a, b])` between regular values, a tangent vector `v` of the band points
outward exactly when the derivative of `f` is positive on it. -/
theorem isOutwardPointing_scalarRegularBand_iff_of_eq_right {x : f ⁻¹' Icc a b} (hx : f x = b)
    (v : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x v ↔ 0 < mvfderiv (𝓡∂ (n + 1)) (fun w : f ⁻¹' Icc a b ↦ f w) x v := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  have hxb : x ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [boundary_scalarRegularBand hn ha hb le_rfl hf hab]
    exact Or.inr hx
  -- The inward coordinate of the preferred chart at the upper face is `b - f`.
  have hchart (w) (hw : w ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
      (chartAt (EuclideanHalfSpace (n + 1)) x w).1 0 = -1 * (f w - b) := by
    rw [scalarRegularBandChartedSpace_chartAt] at hw ⊢
    rw [scalarRegularBandChartAt_apply_zero_of_eq_right hf hn ha hb hab hx hw]
    ring
  rw [isOutwardPointing_iff_mul_mvfderiv_neg hxb (by norm_num)
    (Filter.eventually_of_mem (chart_source_mem_nhds _ x) hchart), neg_one_mul, neg_lt_zero]

end Band

end TauCeti
