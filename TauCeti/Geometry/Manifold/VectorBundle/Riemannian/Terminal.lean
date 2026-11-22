/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Topology.UniformSpace.UniformConvergence.Terminal
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Terminal convergence of evolving Riemannian metrics

Compact convergence of the actual coordinate derivatives of evolving smooth Riemannian metrics
before a terminal time extends through that time if the limit metric curve is left-continuous
and the time derivatives of the coordinate jets have eventual compact-local bounds. The mean
value theorem supplies the time-Lipschitz estimates, and the same filter converges at every time
in the native chart `C^k` topology. In particular `k = ⊤` controls every spatial derivative.

These are the terminal coordinate-jet conclusions used after selecting an interior limit in
pointed compactness of ancient flows. The metrics are native tangent-bundle metrics on a common
manifold. Constructing pointed embeddings, extracting an interior limit, and deriving the bounds
from the Ricci-flow equation are separate steps.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 9.64.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

noncomputable section

open Bundle Filter Set Topology
open scoped ContDiff Manifold NNReal

namespace Bundle.ContMDiffRiemannianMetric

-- Insert canonical operator norms into public signatures, as in the native chart topology.
-- Caching them locally keeps elaboration of nested multilinear operator spaces tractable.
local macro "withMetricOperatorNorms " E:term " in " t:term : term =>
  `(letI : NormedAddCommGroup ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup ($E →L[ℝ] $E →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] $E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    $t)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} {l : Filter ι}
  {g : ι → ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g₀ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {b : ℝ}

omit [I.Boundaryless] in
/-- The spatial chart jets of native metric curves converge on compact sets through the terminal
time. Bounds on their time derivatives provide the required time-Lipschitz estimates. -/
theorem tendstoUniformlyOn_iteratedFDeriv_chartMetric_Iic_prod (x : M) (m : ℕ) :
    withMetricOperatorNorms E in
    (∀ K : Set (ℝ × E), IsCompact K → K ⊆ Iio b ×ˢ (extChartAt I x).target →
      TendstoUniformlyOn
        (fun i p ↦ iteratedFDeriv ℝ m ((g i p.1).toNondegenerateMetric.chartMetric x) p.2)
        (fun p ↦ iteratedFDeriv ℝ m ((g₀ p.1).toNondegenerateMetric.chartMetric x) p.2) l K) →
    (∀ z ∈ (extChartAt I x).target, ContinuousWithinAt
      (fun t ↦ iteratedFDeriv ℝ m ((g₀ t).toNondegenerateMetric.chartMetric x) z) (Iio b) b) →
    (∀ V : Set E, IsCompact V → V ⊆ (extChartAt I x).target →
      ∃ a < b, ∃ L : ℝ≥0, ∀ᶠ i in l, ∀ z ∈ V,
        DifferentiableOn ℝ
          (fun t ↦ iteratedFDeriv ℝ m ((g i t).toNondegenerateMetric.chartMetric x) z) (Icc a b) ∧
        ∀ t ∈ Icc a b, ‖derivWithin
          (fun s ↦ iteratedFDeriv ℝ m ((g i s).toNondegenerateMetric.chartMetric x) z)
          (Icc a b) t‖₊ ≤ L) →
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Iic b ×ˢ (extChartAt I x).target →
      TendstoUniformlyOn
        (fun i p ↦ iteratedFDeriv ℝ m ((g i p.1).toNondegenerateMetric.chartMetric x) p.2)
        (fun p ↦ iteratedFDeriv ℝ m ((g₀ p.1).toNondegenerateMetric.chartMetric x) p.2) l K := by
  intro hconv hg htime K hK hKx
  apply TauCeti.tendstoUniformlyOn_of_lipschitzOnWith_of_subset_Iic_prod hconv hg ?_ hK hKx
  intro V hV hVx
  obtain ⟨a, hab, L, hL⟩ := htime V hV hVx
  refine ⟨a, hab, L, hL.mono fun i hi z hz ↦ ?_⟩
  exact (convex_Icc a b).lipschitzOnWith_of_nnNorm_derivWithin_le (hi z hz).1 (hi z hz).2

/-- Interior convergence of metric jets, left-continuity of the limiting metric curve, and
compact-local time derivative bounds imply convergence in the native chart `C^k` topology at
every time up to the terminal time. The filter, and hence a selected subsequence, is preserved. -/
theorem tendsto_chartCk_of_interior_of_bound_timeDeriv (k : ℕ∞) :
    withMetricOperatorNorms E in
    letI := chartCkTopology (I := I) (M := M) k
    (∀ (x : M) (m : ℕ), (m : ℕ∞) ≤ k →
      ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Iio b ×ˢ (extChartAt I x).target →
        TendstoUniformlyOn
          (fun i p ↦ iteratedFDeriv ℝ m ((g i p.1).toNondegenerateMetric.chartMetric x) p.2)
          (fun p ↦ iteratedFDeriv ℝ m ((g₀ p.1).toNondegenerateMetric.chartMetric x) p.2) l K) →
    ContinuousWithinAt g₀ (Iio b) b →
    (∀ (x : M) (m : ℕ), (m : ℕ∞) ≤ k →
      ∀ V : Set E, IsCompact V → V ⊆ (extChartAt I x).target →
        ∃ a < b, ∃ L : ℝ≥0, ∀ᶠ i in l, ∀ z ∈ V,
          DifferentiableOn ℝ
            (fun t ↦ iteratedFDeriv ℝ m ((g i t).toNondegenerateMetric.chartMetric x) z)
            (Icc a b) ∧
          ∀ t ∈ Icc a b, ‖derivWithin
            (fun s ↦ iteratedFDeriv ℝ m ((g i s).toNondegenerateMetric.chartMetric x) z)
            (Icc a b) t‖₊ ≤ L) →
    ∀ t ≤ b, Tendsto (fun i ↦ g i t) l (𝓝 (g₀ t)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  intro hconv hg htime t ht
  apply (tendsto_chartCk_iff k).mpr
  intro x m hm K hKx hK
  have hcont (z : E) (hz : z ∈ (extChartAt I x).target) : ContinuousWithinAt
      (fun t ↦ iteratedFDeriv ℝ m ((g₀ t).toNondegenerateMetric.chartMetric x) z) (Iio b) b := by
    have hc := (continuous_eval_const (⟨z, hz⟩ : (extChartAt I x).target)).comp
      (continuous_chartMetricDerivative k x hm)
    have heq : (fun t ↦ (g₀ t).chartMetricDerivative x m ⟨z, hz⟩) =
        (fun t ↦ iteratedFDeriv ℝ m ((g₀ t).toNondegenerateMetric.chartMetric x) z) :=
      funext fun t ↦ chartMetricDerivative_apply (g₀ t) x m ⟨z, hz⟩
    rw [← heq]
    exact hc.continuousAt.comp_continuousWithinAt hg
  have hjet := tendstoUniformlyOn_iteratedFDeriv_chartMetric_Iic_prod x m
    (hconv x m hm) hcont (htime x m hm)
    ({t} ×ˢ K) (isCompact_singleton.prod hK)
    (prod_mono (singleton_subset_iff.mpr ht) hKx)
  exact (hjet.comp (fun z ↦ (t, z))).mono fun z hz ↦ ⟨mem_singleton _, hz⟩

end Bundle.ContMDiffRiemannianMetric
