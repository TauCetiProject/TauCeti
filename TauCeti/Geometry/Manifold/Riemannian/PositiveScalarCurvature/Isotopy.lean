/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.ContinuousMap.LocallyConvex
public import TauCeti.Analysis.LocallyConvex.Path
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.SmoothPath
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Interpolation

/-!
# Isotopic metrics of positive scalar curvature are concordant

Two metrics `g₀` and `g₁` of positive scalar curvature on `M` are *isotopic* when they are joined
by a continuous path of metrics of positive scalar curvature. Here continuity is taken in the
chart C² topology `Bundle.ContMDiffRiemannianMetric.chartC2Topology`, so every path that is
continuous for a finer topology, such as the smooth topology, qualifies. On a compact manifold
without boundary, isotopic metrics are concordant.

The proof first replaces the path by a smooth one. The chart C² topology is induced by the
coordinate derivatives of orders zero, one and two, which take values in a product of
compact-open spaces of continuous maps into normed spaces. That product is a locally convex
space, and positive scalar curvature is an open condition
(`Bundle.ContMDiffRiemannianMetric.isOpen_setOf_hasPositiveScalarCurvature_chartC2`). So
`ContinuousMap.exists_smooth_convexCombination_mem` approximates the path by finite convex
combinations `∑ i, w i t • g (s i)` of its values, with smooth weights `w i`, which keep positive
scalar curvature and agree with the endpoints for `t ≤ 1 / 3` and for `t ≥ 2 / 3`. The coordinate
derivatives of such a combination are the same combinations of coordinate derivatives
(`Bundle.ContMDiffRiemannianMetric.iteratedFDeriv_chartMetric_weightedMeanRiemannianMetric_const`),
so the approximation is computed by actual metrics. Weighting the cylinder metrics
`g (s i) + dt²` by the same functions of `t` gives a smooth metric on `M × ℝ` which is
`(∑ i, w i t • g (s i)) + dt²` at `(x, t)`. Running this smooth path slowly gives a concordance
(`Bundle.ContMDiffRiemannianMetric.concordant_of_forall_inner_eq_cylinder`).

## Main results

* `Bundle.ContMDiffRiemannianMetric.exists_forall_inner_eq_cylinder_of_joinedIn`: a continuous
  path of metrics of positive scalar curvature on a compact manifold can be replaced by a smooth
  path of such metrics with the same ends, constant for `t ≤ 0` and for `t ≥ 1`.
* `Bundle.ContMDiffRiemannianMetric.concordant_of_joinedIn`: isotopic metrics of positive scalar
  curvature on a compact manifold are concordant.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* S. Stolz, *Positive scalar curvature—constructions and obstructions*, arXiv:2202.05904, for
  the statement that isotopic metrics of positive scalar curvature are concordant.
-/

open Bundle Set Topology
open scoped ContDiff Manifold TauCeti.MetricC2

public section

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Cache the canonical operator-space instances, as in the definition of the chart C² topology:
-- otherwise instance search for the algebraic and topological structure on the nested operator
-- spaces receiving the derivatives of chart metrics exhausts its heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Smoothing an isotopy.** On a compact manifold without boundary, let `g₀` and `g₁` be joined
by a path of metrics of positive scalar curvature, continuous in the chart C² topology. Then there
is a path `t ↦ g t` of metrics of positive scalar curvature, from `g₀` for `t ≤ 0` to `g₁` for
`t ≥ 1`, which is smooth in the sense that some smooth metric on `M × ℝ` is the cylinder metric
`g t + dt²` at every point `(x, t)`. -/
theorem exists_forall_inner_eq_cylinder_of_joinedIn [CompactSpace M]
    {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (h : JoinedIn {g | g.HasPositiveScalarCurvature} g₀ g₁) :
    ∃ (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
        (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))
      (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)),
      (∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) ∧
        (∀ t, (g t).HasPositiveScalarCurvature) ∧ (∀ t ≤ 0, g t = g₀) ∧
        ∀ t, 1 ≤ t → g t = g₁ := by
  obtain ⟨γ, hγ⟩ := h
  -- The chart C² topology is induced by the coordinate derivatives through order two, which
  -- take values in a locally convex space. Index them by pairs `(x, m)`, and cache the
  -- instances on each factor: otherwise instance search for the additive structure and scalar
  -- multiplication of the product runs through the normed-group instances and exhausts its
  -- heartbeats.
  let iG (q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) :
      AddCommGroup C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
    inferInstance
  let (q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) :
      AddCommMonoid C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
    (iG q).toAddCommMonoid
  let (q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) :
      SMul ℝ C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
    inferInstance
  let (q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) :
      Module ℝ C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
    inferInstance
  let (q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) :
      LocallyConvexSpace ℝ C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
    ContinuousMap.instLocallyConvexSpace
  let Φ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) →
      ((q : M × {m : ℕ // (m : ℕ∞) ≤ 2}) →
        C((extChartAt I q.1).target, E [×q.2]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))) :=
    fun g q ↦ g.chartMetricDerivative q.1 q.2
  have hΦ : IsInducing Φ := isInducing_chartMetricDerivative 2
  obtain ⟨U, hU, hUS⟩ := hΦ.isOpen_iff.1 isOpen_setOf_hasPositiveScalarCurvature_chartC2
  have hγU (t : unitInterval) : Φ (γ t) ∈ U := mem_preimage.1 (hUS ▸ hγ t)
  -- Approximate the path by finite convex combinations of its values, with smooth weights.
  obtain ⟨s, w, hw, hw₀, hw₁, hleft, hright, hmem⟩ :=
    ContinuousMap.exists_smooth_convexCombination_mem
      ⟨Φ ∘ γ, hΦ.continuous.comp γ.continuous⟩ hU hγU
  let g (t : ℝ) := TauCeti.weightedMeanRiemannianMetric (fun i : s ↦ γ i.1) (fun i _ ↦ w i t)
    (fun _ ↦ contMDiff_const) (fun i _ ↦ hw₀ i t) fun _ ↦ hw₁ t
  -- These combinations of metrics are computed by the same combinations of chart derivatives.
  have hΦg (t : ℝ) : Φ (g t) = ∑ i, w i t • Φ (γ i.1) := by
    funext q
    ext z : 1
    -- Restate `chartMetricDerivative_apply` with the chart target in the form appearing here.
    have happly (g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
        g'.chartMetricDerivative q.1 q.2 z =
          iteratedFDeriv ℝ q.2 (g'.toNondegenerateMetric.chartMetric q.1) z :=
      chartMetricDerivative_apply g' q.1 q.2 z
    simp only [Φ, happly, Finset.sum_apply, Pi.smul_apply, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply]
    exact iteratedFDeriv_chartMetric_weightedMeanRiemannianMetric_const (fun i : s ↦ γ i.1)
      (fun i ↦ w i t) q.1 q.2 z.2
  have hg₀ (t : ℝ) (ht : t ≤ 1 / 3) : g t = g₀ :=
    hΦ.injective ((hΦg t).trans ((hleft t ht).trans (congrArg Φ γ.source)))
  have hg₁ (t : ℝ) (ht : 2 / 3 ≤ t) : g t = g₁ :=
    hΦ.injective ((hΦg t).trans ((hright t ht).trans (congrArg Φ γ.target)))
  have hpos (t : ℝ) : (g t).HasPositiveScalarCurvature := by
    have hmem' : g t ∈ Φ ⁻¹' U := by
      rw [mem_preimage, hΦg]
      exact hmem t
    rwa [hUS] at hmem'
  -- Weighting the cylinder metrics by the same functions of `t` gives the smooth metric on
  -- `M × ℝ`, since the weights sum to one.
  refine ⟨TauCeti.weightedMeanRiemannianMetric (fun i : s ↦ (γ i.1).cylinder)
    (fun i p ↦ w i p.2) (fun i ↦ (hw i).contMDiff.comp contMDiff_snd) (fun i p ↦ hw₀ i p.2)
    (fun p ↦ hw₁ p.2), g, fun p ↦ ?_, hpos, fun t ht ↦ hg₀ t (by linarith),
    fun t ht ↦ hg₁ t (by linarith)⟩
  ext v v'
  simp only [TauCeti.weightedMeanRiemannianMetric_inner, cylinder_inner, g, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, hw₁, one_mul]

/-- **Isotopic metrics of positive scalar curvature are concordant.** On a compact manifold without
boundary, two metrics joined by a path of metrics of positive scalar curvature, continuous in the
chart C² topology, are concordant. -/
theorem concordant_of_joinedIn [CompactSpace M]
    {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (h : JoinedIn {g | g.HasPositiveScalarCurvature} g₀ g₁) : Concordant g₀ g₁ := by
  obtain ⟨G, g, hG, hpos, h₀, h₁⟩ := exists_forall_inner_eq_cylinder_of_joinedIn h
  have hc := concordant_of_forall_inner_eq_cylinder hG (fun t _ ↦ hpos t)
    (fun t ht ↦ (h₀ t ht).trans (h₀ 0 le_rfl).symm)
    (fun t ht ↦ (h₁ t ht).trans (h₁ 1 le_rfl).symm)
  rwa [h₀ 0 le_rfl, h₁ 1 le_rfl] at hc

end Bundle.ContMDiffRiemannianMetric
