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
boundary for its atlas `TauCeti.scalarRegularSublevelChartedSpace`, and its boundary is the level
`f⁻¹(a)` (`TauCeti.boundary_scalarRegularSublevel`). The function `f` co-orients this boundary,
without any choice of metric: a tangent vector `v` of the sublevel at a point of the level points
outward (`TauCeti.IsOutwardPointing`) exactly when `df(v) > 0`, where `df` is the derivative of
the restriction of `f` to the sublevel
(`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mvfderiv_pos`).

For a band `f⁻¹([a, b])` between regular values `a < b`, with atlas
`TauCeti.scalarRegularBandChartedSpace`, the function increases out of the band through its upper
face and decreases out of it through its lower face: at a point of `f⁻¹(b)` a tangent vector points
outward exactly when `df(v) > 0`
(`TauCeti.isOutwardPointing_scalarRegularBand_iff_mvfderiv_pos_of_eq_right`), and at a point of
`f⁻¹(a)` exactly when `df(v) < 0`
(`TauCeti.isOutwardPointing_scalarRegularBand_iff_mvfderiv_neg_of_eq_left`).

In each case the zeroth coordinate of the preferred chart at a boundary point, the inward
coordinate, is `a - f`, `b - f` or `f - a`, so these statements are instances of
`TauCeti.isOutwardPointing_iff_mvfderiv_pos`. Through `TauCeti.boundaryOrientation_spec` they
describe the outward-first orientation which an orientation of the sublevel or band induces on its
boundary levels, with `v` any vector on which `df` has the appropriate sign.

## Main results

* `TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mvfderiv_pos`: outward vectors of
  `{f ≤ a}` are those with `df(v) > 0`.
* `TauCeti.isOutwardPointing_scalarRegularBand_iff_mvfderiv_neg_of_eq_left`: outward vectors of
  `f⁻¹([a, b])` at the lower level are those with `df(v) < 0`.
* `TauCeti.isOutwardPointing_scalarRegularBand_iff_mvfderiv_pos_of_eq_right`: outward vectors of
  `f⁻¹([a, b])` at the upper level are those with `df(v) > 0`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 5 (outward-pointing vectors and boundary defining functions, and
  Proposition 5.47 on regular sublevel sets).
-/

public section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  {n : ℕ} [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  (hf : ContMDiff I 𝓘(ℝ) 1 f) (hn : Module.finrank ℝ E = n + 1)

/-- **The outward co-orientation of a regular sublevel.** At a point `x` of the level `f⁻¹(a)`,
a tangent vector `v` of the sublevel `{f ≤ a}` points outward exactly when `df(v) > 0`, where
`df` is the derivative of the restriction of `f` to the sublevel. -/
theorem isOutwardPointing_scalarRegularSublevel_iff_mvfderiv_pos
    (hreg : IsRegularValue I 𝓘(ℝ) f a) {x : {x | f x ≤ a}} (hx : f x = a) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    ∀ v : TangentSpace (𝓡∂ (n + 1)) x,
      IsOutwardPointing x v ↔ 0 < mvfderiv (𝓡∂ (n + 1)) (fun w : {x | f x ≤ a} ↦ f w) x v := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  intro v
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  have hbd : x ∈ (𝓡∂ (n + 1)).boundary {x | f x ≤ a} := by
    rw [boundary_scalarRegularSublevel hreg hn le_rfl hf]
    exact hx
  refine isOutwardPointing_iff_mvfderiv_pos hbd (c := a) ?_ v
  -- The inward coordinate of the preferred chart at `x` is `a - f`.
  filter_upwards [chart_source_mem_nhds (EuclideanHalfSpace (n + 1)) x] with w hw
  rw [scalarRegularSublevelChartedSpace_chartAt] at hw
  rw [extChartAt_coe, Function.comp_apply, scalarRegularSublevelChartedSpace_chartAt,
    modelWithCornersEuclideanHalfSpace_toFun]
  exact scalarRegularSublevelChartAt_apply_zero_of_eq hf hreg hn hx hw

section Band

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- **The outward co-orientation of a band at its lower level.** At a point `x` of the lower level
`f⁻¹(a)` of the band `f⁻¹([a, b])` between regular values `a < b`, a tangent vector `v` of the
band points outward exactly when `df(v) < 0`, where `df` is the derivative of the restriction of
`f` to the band. -/
theorem isOutwardPointing_scalarRegularBand_iff_mvfderiv_neg_of_eq_left {x : f ⁻¹' Icc a b}
    (hx : f x = a) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ∀ v : TangentSpace (𝓡∂ (n + 1)) x,
      IsOutwardPointing x v ↔ mvfderiv (𝓡∂ (n + 1)) (fun w : f ⁻¹' Icc a b ↦ f w) x v < 0 := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  intro v
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  have hbd : x ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [boundary_scalarRegularBand hn ha hb le_rfl hf hab]
    exact Or.inl hx
  -- The inward coordinate of the preferred chart at `x` is `f - a = -a - (-f)`.
  rw [isOutwardPointing_iff_mvfderiv_pos hbd (g := fun w : f ⁻¹' Icc a b ↦ -f w) (c := -a),
    mvfderiv_fun_neg, neg_apply, neg_pos]
  filter_upwards [chart_source_mem_nhds (EuclideanHalfSpace (n + 1)) x] with w hw
  rw [scalarRegularBandChartedSpace_chartAt] at hw
  rw [extChartAt_coe, Function.comp_apply, scalarRegularBandChartedSpace_chartAt,
    modelWithCornersEuclideanHalfSpace_toFun,
    scalarRegularBandChartAt_apply_zero_of_eq_left hf hn ha hb hx hw]
  ring

/-- **The outward co-orientation of a band at its upper level.** At a point `x` of the upper level
`f⁻¹(b)` of the band `f⁻¹([a, b])` between regular values `a < b`, a tangent vector `v` of the
band points outward exactly when `df(v) > 0`, where `df` is the derivative of the restriction of
`f` to the band. -/
theorem isOutwardPointing_scalarRegularBand_iff_mvfderiv_pos_of_eq_right {x : f ⁻¹' Icc a b}
    (hx : f x = b) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ∀ v : TangentSpace (𝓡∂ (n + 1)) x,
      IsOutwardPointing x v ↔ 0 < mvfderiv (𝓡∂ (n + 1)) (fun w : f ⁻¹' Icc a b ↦ f w) x v := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  intro v
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  have hbd : x ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [boundary_scalarRegularBand hn ha hb le_rfl hf hab]
    exact Or.inr hx
  refine isOutwardPointing_iff_mvfderiv_pos hbd (c := b) ?_ v
  -- The inward coordinate of the preferred chart at `x` is `b - f`.
  filter_upwards [chart_source_mem_nhds (EuclideanHalfSpace (n + 1)) x] with w hw
  rw [scalarRegularBandChartedSpace_chartAt] at hw
  rw [extChartAt_coe, Function.comp_apply, scalarRegularBandChartedSpace_chartAt,
    modelWithCornersEuclideanHalfSpace_toFun]
  exact scalarRegularBandChartAt_apply_zero_of_eq_right hf hn ha hb hab hx hw

end Band

end TauCeti
