/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Pullback
public import TauCeti.Geometry.Manifold.SMulGroupoid

/-!
# The Riemannian metric of an `(Isom X, X)`-manifold

Let `X` be a Riemannian manifold and `M` an `(Isom X, X)`-manifold: a space with an `X`-valued
atlas whose transition maps are locally Riemannian isometries of `X`
(`[ChartedSpace X M] [HasGroupoid M (smulGroupoid (Isom I X) X)]`). For a model geometry `X`,
this is a geometric structure on `M` modelled on `X`. Such an `M` inherits a Riemannian metric
from `X`: read the metric of `X` through any chart. The transition maps preserve the metric of
`X`, so the result does not depend on the chart, and it is the unique metric on `M` for which every
chart is a local isometry. This is the metric with respect to which completeness of the geometric
structure is measured (Thurston, Proposition 3.4.15).

Throughout, `M` carries the composite charts `ChartedSpace.comp H X M`, obtained by following
its `X`-valued charts with the charts of `X`; this is the smooth structure of
`isManifold_of_hasGroupoid_smulGroupoid`, and it is not an instance, so the statements install it
with `letI`. A `(G, X)`-manifold for a group `G` acting on `X` through Riemannian isometries is an
`(Isom X, X)`-manifold by `smulGroupoid_le`, so everything here applies to it.

## Main definitions

* `TauCeti.chartRiemannianMetric`: the metric of `X` read on `M` through the preferred charts.
* `TauCeti.contMDiffChartRiemannianMetric`: the same metric, bundled with its smoothness: it is
  `C^n` whenever the metric of `X` is.

## Main results

* `TauCeti.chartRiemannianMetric_inner`: at `x`, the metric is the metric of `X` pulled back along
  the derivative of the preferred chart at `x`.
* `TauCeti.inner_mfderiv_of_mem_atlas`: every chart of `M` is a local isometry to `X`.
* `TauCeti.eq_chartRiemannianMetric_iff`: the metric read through the charts is the only Riemannian
  metric on `M` for which every chart is a local isometry.
* `TauCeti.isContMDiffRiemannianBundle_chartRiemannianMetric`: installed as the Riemannian bundle
  structure of `M`, the metric is `C^n` whenever the metric of `X` is.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton University Press,
  1997, Section 3.3 ((G, X)-manifolds) and Section 3.4 (the metric a (G, X)-manifold inherits from
  a `G`-invariant metric on `X`, Proposition 3.4.15).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace X M]

/-! ### The metric read through the charts -/

variable (I X M) in
/-- The Riemannian metric of `X` read on `M` through its preferred `X`-valued charts: at `x`, it is
the inner product of `X` at `chartAt X x x`. The tangent spaces of `M` are those of the composite
charts `ChartedSpace.comp H X M`. -/
def chartRiemannianMetric :
    letI := ChartedSpace.comp H X M
    RiemannianMetric (fun x : M ↦ TangentSpace I x) :=
  letI := ChartedSpace.comp H X M
  { inner x := (RiemannianBundle.g (E := fun p : X ↦ TangentSpace I p)).inner (chartAt X x x)
    symm x := RiemannianBundle.g.symm (E := fun p : X ↦ TangentSpace I p) (chartAt X x x)
    pos x := RiemannianBundle.g.pos (E := fun p : X ↦ TangentSpace I p) (chartAt X x x)
    continuousAt x :=
      RiemannianBundle.g.continuousAt (E := fun p : X ↦ TangentSpace I p) (chartAt X x x)
    isVonNBounded x :=
      RiemannianBundle.g.isVonNBounded (E := fun p : X ↦ TangentSpace I p) (chartAt X x x) }

/-- At `x`, the metric read through the charts is the metric of `X` pulled back along the
derivative of the preferred chart at `x`. -/
@[simp]
theorem chartRiemannianMetric_inner (x : M) :
    letI := ChartedSpace.comp H X M
    ∀ v w : TangentSpace I x, (chartRiemannianMetric I X M).inner x v w =
      inner ℝ (mfderiv I I (chartAt X x) x v) (mfderiv I I (chartAt X x) x w) := by
  let := ChartedSpace.comp H X M
  intro v w
  -- The derivative of the preferred chart at `x` is the identity, and the inner product of `X` at
  -- `chartAt X x x` is the metric of `M` at `x` by definition.
  rw [(hasMFDerivAt_chartAt_comp x).mfderiv]
  exact rfl

variable [HasGroupoid M (smulGroupoid (Isom I X) X)]

/-- Every chart of an `(Isom X, X)`-manifold is a local isometry from the metric read through the
charts to the metric of `X`. -/
theorem inner_mfderiv_of_mem_atlas {e : OpenPartialHomeomorph M X} (he : e ∈ atlas X M) {y : M}
    (hy : y ∈ e.source) :
    letI := ChartedSpace.comp H X M
    ∀ v w : TangentSpace I y, inner ℝ (mfderiv I I e y v) (mfderiv I I e y w) =
      (chartRiemannianMetric I X M).inner y v w := by
  let := ChartedSpace.comp H X M
  intro v w
  -- Near `y`, the chart `e` is an isometry `γ` of `X` after the preferred chart at `y`, whose
  -- derivative at `y` is the identity.
  obtain ⟨γ, hγ⟩ := exists_smul_eventuallyEq_chartAt (G := Isom I X) he hy
  have hd := (((γ.mdifferentiableAt _).hasMFDerivAt.comp y
    (hasMFDerivAt_chartAt_comp y)).congr_of_eventuallyEq hγ).mfderiv
  rw [hd, hγ.eq_of_nhds]
  exact γ.inner_mfderiv (chartAt X y y) v w

/-- The metric read through the charts is the only Riemannian metric on an `(Isom X, X)`-manifold
for which every chart is a local isometry to `X`. -/
theorem eq_chartRiemannianMetric_iff
    (g : letI := ChartedSpace.comp H X M; RiemannianMetric (fun x : M ↦ TangentSpace I x)) :
    letI := ChartedSpace.comp H X M
    g = chartRiemannianMetric I X M ↔ ∀ e ∈ atlas X M, ∀ y ∈ e.source, ∀ v w : TangentSpace I y,
      inner ℝ (mfderiv I I e y v) (mfderiv I I e y w) = g.inner y v w := by
  let := ChartedSpace.comp H X M
  refine ⟨fun hg e he y hy v w ↦ hg ▸ inner_mfderiv_of_mem_atlas he hy v w, fun h ↦ ?_⟩
  obtain ⟨inner, symm, pos, continuousAt, isVonNBounded⟩ := g
  obtain rfl : inner = (chartRiemannianMetric I X M).inner := by
    funext y
    ext v w
    rw [← h _ (chart_mem_atlas X y) y (mem_chart_source X y), chartRiemannianMetric_inner]
  rfl

/-! ### Smoothness -/

variable [IsManifold I 1 X] {n : ℕ∞ω}
  [IsContMDiffRiemannianBundle I n E (fun x : X ↦ TangentSpace I x)]

variable (I X M n) in
/-- The metric of an `(Isom X, X)`-manifold read through its charts, bundled as a `C^n` Riemannian
metric for the smooth structure of the composite charts, when the metric of `X` is `C^n`. -/
def contMDiffChartRiemannianMetric :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) :=
  letI := ChartedSpace.comp H X M
  haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
  { chartRiemannianMetric I X M with
    contMDiff x₀ := by
      -- Near `x₀` the metric is the metric of `X` pulled back along the preferred chart at `x₀`,
      -- which is `C^(n+1)` at `x₀`.
      apply ((ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := n) (F := E)
        (V := fun p : X ↦ TangentSpace I p)).contMDiffAt_pullback
        (contMDiffAt_chartAt_comp x₀)).congr_of_eventuallyEq
      filter_upwards [(chartAt X x₀).open_source.mem_nhds (mem_chart_source X x₀)] with y hy
      congr 1
      ext v w
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.precomp_apply,
        ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
      exact (inner_mfderiv_of_mem_atlas (chart_mem_atlas X x₀) hy v w).symm }

/-- The inner product of `contMDiffChartRiemannianMetric` is that of the metric read through the
charts. -/
@[simp]
theorem contMDiffChartRiemannianMetric_inner :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
    (contMDiffChartRiemannianMetric I X M n).inner = (chartRiemannianMetric I X M).inner :=
  (rfl)

/-- Forgetting smoothness of `contMDiffChartRiemannianMetric` gives the metric read through the
charts. -/
@[simp]
theorem contMDiffChartRiemannianMetric_toRiemannianMetric :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
    (contMDiffChartRiemannianMetric I X M n).toRiemannianMetric = chartRiemannianMetric I X M :=
  (rfl)

/-- Installed as the Riemannian bundle structure of an `(Isom X, X)`-manifold, the metric read
through the charts is `C^n` whenever the metric of `X` is. -/
theorem isContMDiffRiemannianBundle_chartRiemannianMetric :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨chartRiemannianMetric I X M⟩
    IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
  letI := ChartedSpace.comp H X M
  haveI := isManifold_of_hasGroupoid_smulGroupoid I 1 (Isom I X) (X := X) M
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨chartRiemannianMetric I X M⟩
  ⟨(contMDiffChartRiemannianMetric I X M n).inner,
    (contMDiffChartRiemannianMetric I X M n).contMDiff, fun _ _ _ ↦ rfl⟩

end TauCeti
