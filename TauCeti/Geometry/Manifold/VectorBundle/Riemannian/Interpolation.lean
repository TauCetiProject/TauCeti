/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology

/-!
# Convex interpolation of Riemannian metrics

`Bundle.ContMDiffRiemannianMetric.convexCombination g h t` is the metric
`(1 - t) g + t h`, for `t` in the unit interval. The construction uses the convex cone of
positive symmetric bilinear sections, and allows arbitrary regularity and boundary charts.
It preserves the metric at every point where the two input metrics agree.

For smooth tangent metrics on a boundaryless manifold, interpolation is jointly continuous
in both metrics and the interval parameter for the chart C² topology. The coordinate
derivatives of every order interpolate linearly. These facts allow local combinations of
metrics in approximation arguments, including arguments relative to a fixed spatial region.
They do not assert that scalar positivity is preserved by convex combinations.

The ambient section space and its positive cone are those of
`Bundle.ContMDiffRiemannianMetric.positiveDefiniteSectionEquiv`.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

section VectorBundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Convex interpolation of two finite-rank Riemannian metrics, with weights `1 - t` and `t`.
This preserves positive definiteness, not necessarily positive scalar curvature. -/
def convexCombination (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    ContMDiffRiemannianMetric IB n F V :=
  ofPositiveDefiniteSection ((1 - (t : ℝ)) • g.toBilinearSection +
    (t : ℝ) • h.toBilinearSection)
    (TauCeti.Manifold.convex_positiveDefiniteBilinearSections
      g.toBilinearSection_mem h.toBilinearSection_mem
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ)))

/-- The underlying section of an interpolated metric is the same convex combination. -/
@[simp]
theorem toBilinearSection_convexCombination
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    (g.convexCombination h t).toBilinearSection =
      (1 - (t : ℝ)) • g.toBilinearSection + (t : ℝ) • h.toBilinearSection := by
  simp [convexCombination]

/-- The inner product of an interpolated metric is the weighted sum of inner products. -/
@[simp]
theorem convexCombination_inner
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) (x : B) (v w : V x) :
    (g.convexCombination h t).inner x v w =
      (1 - (t : ℝ)) * g.inner x v w + (t : ℝ) * h.inner x v w := by
  simp [convexCombination]

/-- Interpolation starts at the first metric. -/
@[simp]
theorem convexCombination_zero (g h : ContMDiffRiemannianMetric IB n F V) :
    g.convexCombination h 0 = g := by
  ext x v w
  simp

/-- Interpolation ends at the second metric. -/
@[simp]
theorem convexCombination_one (g h : ContMDiffRiemannianMetric IB n F V) :
    g.convexCombination h 1 = h := by
  ext x v w
  simp

/-- Interpolating a metric with itself leaves it unchanged. -/
@[simp]
theorem convexCombination_self (g : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    g.convexCombination g t = g := by
  ext x v w
  simp only [convexCombination_inner]
  ring

/-- At any point where the two metrics agree, interpolation fixes their common inner product.
In particular, interpolation preserves prescribed data on a neighbourhood of a closed subset. -/
theorem convexCombination_inner_eq_of_eq
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) {x : B}
    (hx : g.inner x = h.inner x) : (g.convexCombination h t).inner x = g.inner x := by
  ext v w
  rw [convexCombination_inner, ← hx]
  ring

end VectorBundle

section TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Cache the canonical operator norms, as in the chart C² topology module: inference for
-- iterated multilinear maps into nested operator spaces otherwise exhausts heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] in
/-- On a chart target, the coordinate bilinear form of an interpolated metric is the
interpolation of the coordinate bilinear forms. -/
theorem chartMetric_convexCombination
    (g h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (t : unitInterval) (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.convexCombination h t).toNondegenerateMetric.chartMetric x z =
      (1 - (t : ℝ)) • g.toNondegenerateMetric.chartMetric x z +
        (t : ℝ) • h.toNondegenerateMetric.chartMetric x z := by
  ext v w
  simp only [(g.convexCombination h t).toNondegenerateMetric.chartMetric_apply hz,
    g.toNondegenerateMetric.chartMetric_apply hz, h.toNondegenerateMetric.chartMetric_apply hz,
    toNondegenerateMetric_apply, convexCombination_inner, add_apply, smul_apply, smul_eq_mul]

/-- Every coordinate derivative of an interpolated metric is the corresponding weighted sum.
The weights are constant in the spatial variable. -/
theorem iteratedFDeriv_chartMetric_convexCombination
    (g h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (t : unitInterval) (x : M) (m : ℕ) {z : E} (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m ((g.convexCombination h t).toNondegenerateMetric.chartMetric x) z =
      (1 - (t : ℝ)) • iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z +
        (t : ℝ) • iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric x) z := by
  have hg := (g.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hz)
  have hh := (h.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hz)
  have heq : (g.convexCombination h t).toNondegenerateMetric.chartMetric x =ᶠ[𝓝 z]
      (fun y ↦ (1 - (t : ℝ)) • g.toNondegenerateMetric.chartMetric x y +
        (t : ℝ) • h.toNondegenerateMetric.chartMetric x y) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartMetric_convexCombination g h t x hy
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds,
    fun_iteratedFDeriv_add_apply ((hg.of_le (by simp)).const_smul _)
      ((hh.of_le (by simp)).const_smul _),
    iteratedFDeriv_const_smul_apply' (hg.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hh.of_le (by simp))]

open scoped TauCeti.MetricC2

/-- C²-continuous families remain C²-continuous under convex interpolation with a continuous
interval-valued parameter. Both endpoint metrics may vary. -/
@[fun_prop]
theorem continuous_convexCombination {P : Type*} [TopologicalSpace P]
    {g h : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {t : P → unitInterval} (hg : Continuous g) (hh : Continuous h) (ht : Continuous t) :
    Continuous (fun p ↦ (g p).convexCombination (h p) (t p)) := by
  rw [continuous_chartCk_iff] at hg hh ⊢
  intro x m hm
  have hformula : (fun q : P × (extChartAt I x).target ↦
      iteratedFDeriv ℝ m ((g q.1).convexCombination (h q.1) (t q.1)
        |>.toNondegenerateMetric.chartMetric x) q.2) =
      (fun q : P × (extChartAt I x).target ↦
        (1 - (t q.1 : ℝ)) • iteratedFDeriv ℝ m ((g q.1).toNondegenerateMetric.chartMetric x) q.2 +
        (t q.1 : ℝ) • iteratedFDeriv ℝ m ((h q.1).toNondegenerateMetric.chartMetric x) q.2) := by
    funext q
    exact iteratedFDeriv_chartMetric_convexCombination _ _ _ _ _ q.2.property
  rw [hformula]
  have hc : Continuous (fun q : P × (extChartAt I x).target ↦ (t q.1 : ℝ)) :=
    ht.subtype_val.comp continuous_fst
  have hleft := ((continuous_const (y := (1 : ℝ))).sub hc).smul (hg x m hm)
  have hright := hc.smul (hh x m hm)
  exact hleft.add hright

end TangentBundle

end Bundle.ContMDiffRiemannianMetric
