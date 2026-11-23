/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Tactic
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Closed coordinate balls

A closed ball contained in an extended chart target pulls back to a compact subset of the chart
source. Its membership is the closed coordinate-distance inequality, and the corresponding
strict inequality places a point in its interior. No smoothness or Riemannian metric is needed.

Maps into a compact set `K` of a manifold that converge locally uniformly after composing with a
continuous map `e` injective on `K` (for instance an embedding into a vector space) can be read in
a chart: near a point whose limit value lies in the chart source, the limit and the tail of the
sequence take values in a closed coordinate ball inside the chart target.

## Main results

* `TauCeti.Manifold.chart_closedBall_properties`: compactness, membership and interior criteria.
* `IsCompact.exists_closedBall_forall_mem_extChartAt_source`: maps into a compact set converging
  locally uniformly through a continuous injection are eventually in a closed coordinate ball
  near each point.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Set Topology Metric
open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A closed ball contained in a manifold chart pulls back to a compact subset
of the chart source, with the expected membership and interior-ball criteria. -/
theorem chart_closedBall_properties
    (p : M) (c : E) {R : ℝ}
    (hball : closedBall c R ⊆ (extChartAt 𝓘(ℝ, E) p).target) :
    let e := extChartAt 𝓘(ℝ, E) p
    let C := e.symm '' closedBall c R
    IsCompact C ∧ C ⊆ e.source ∧
      (∀ x ∈ e.source, x ∈ C ↔ ‖e x - c‖ ≤ R) ∧
      (∀ x ∈ e.source, ‖e x - c‖ < R → x ∈ interior C) := by
  let e := extChartAt 𝓘(ℝ, E) p
  let C := e.symm '' closedBall c R
  have hC : IsCompact C := (isCompact_closedBall c R).image_of_continuousOn
    ((continuousOn_extChartAt_symm p).mono hball)
  have hCs : C ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hball hz)
  have hmem (x : M) (hx : x ∈ e.source) : x ∈ C ↔ ‖e x - c‖ ≤ R := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [e.right_inv (hball hz)]
      exact mem_closedBall_iff_norm.mp hz
    · intro hnorm
      exact ⟨e x, mem_closedBall_iff_norm.mpr hnorm, e.left_inv hx⟩
  refine ⟨hC, hCs, hmem, ?_⟩
  intro x hx hnorm
  have hO : IsOpen (e.source ∩ e ⁻¹' ball c R) :=
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) isOpen_ball
  have hOC : e.source ∩ e ⁻¹' ball c R ⊆ C := by
    intro y hy
    exact (hmem y hy.1).2 (mem_ball_iff_norm.mp hy.2).le
  exact mem_interior.mpr ⟨e.source ∩ e ⁻¹' ball c R, hOC, hO,
    hx, mem_ball_iff_norm.mpr hnorm⟩


end TauCeti.Manifold

namespace TauCeti

open Filter Function

variable {𝕜 E H M X F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [I.Boundaryless] [PseudoMetricSpace X] [ProperSpace X] [MetricSpace F]

/-- **Localization in a chart.** Let `uₙ` and `v` map an open set `S` of a proper metric space into
a compact set `K` of a manifold, with `v` continuous and `e ∘ uₙ → e ∘ v` locally uniformly on `S`
for a map `e` continuous and injective on `K`. If `v y` lies in the source of the chart at `α`,
there are a closed coordinate ball `B` about `extChartAt I α (v y)` inside the chart target, a
closed ball about `y` inside `S` and an index `N` such that on that ball `v`, and `uₙ` for `n ≥ N`,
take values in the chart source with coordinates in `B`. -/
theorem _root_.IsCompact.exists_closedBall_forall_mem_extChartAt_source {K : Set M} {e : M → F}
    (hK : IsCompact K) (he : ContinuousOn e K) (he_inj : InjOn e K) {S : Set X} (hS : IsOpen S)
    {u : ℕ → X → M} {v : X → M} (huK : ∀ n, MapsTo (u n) S K) (hv : ContinuousOn v S)
    (hvK : MapsTo v S K) (hconv : TendstoLocallyUniformlyOn (fun n ↦ e ∘ u n) (e ∘ v) atTop S)
    {α : M} {y : X} (hy : y ∈ S) (hyα : v y ∈ (extChartAt I α).source) :
    ∃ κ > 0, closedBall (extChartAt I α (v y)) κ ⊆ (extChartAt I α).target ∧
      ∃ r > 0, closedBall y r ⊆ S ∧ ∃ N, ∀ z ∈ closedBall y r,
        (v z ∈ (extChartAt I α).source ∧
          extChartAt I α (v z) ∈ closedBall (extChartAt I α (v y)) κ) ∧
        ∀ n ≥ N, u n z ∈ (extChartAt I α).source ∧
          extChartAt I α (u n z) ∈ closedBall (extChartAt I α (v y)) κ := by
  set φ := extChartAt I α
  -- A closed coordinate ball about `φ (v y)` inside the chart target, and a radius `ε` such that
  -- points of `K` with images through `e` within `ε` of `e (v y)` have coordinates in it.
  obtain ⟨κ, hκ, hκT⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) α) (φ (v y))
    (φ.map_source hyα)
  have hN : φ.source ∩ φ ⁻¹' ball (φ (v y)) (κ / 2) ∈ 𝓝 (v y) :=
    inter_mem (extChartAt_source_mem_nhds' hyα)
      ((continuousAt_extChartAt' hyα).preimage_mem_nhds (ball_mem_nhds _ (half_pos hκ)))
  obtain ⟨V, hV, hVN⟩ := hK.exists_mem_nhds_inter_preimage_subset he he_inj (hvK hy) hN
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  have hin {x : M} (hxK : x ∈ K) (hx : dist (e x) (e (v y)) < ε) :
      x ∈ φ.source ∧ φ x ∈ closedBall (φ (v y)) (κ / 2) :=
    have h := hVN ⟨hxK, hεV (mem_ball.2 hx)⟩
    ⟨h.1, ball_subset_closedBall h.2⟩
  -- A closed ball about `y` on which `e ∘ v` stays within `ε / 2` of `e (v y)`, and an index from
  -- which `e ∘ uₙ` stays within `ε / 2` of `e ∘ v` on it.
  have hev : ContinuousAt (e ∘ v) y :=
    ((he (v y) (hvK hy)).comp (hv y hy) hvK).continuousAt (hS.mem_nhds hy)
  obtain ⟨r₀, hr₀, hr₀S⟩ := Metric.mem_nhds_iff.1 (inter_mem (hS.mem_nhds hy)
    (hev.preimage_mem_nhds (ball_mem_nhds _ (half_pos hε))))
  have hcl : closedBall y (r₀ / 2) ⊆ S ∩ (e ∘ v) ⁻¹' ball (e (v y)) (ε / 2) :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hr₀S
  obtain ⟨N, hNe⟩ := eventually_atTop.1 (hconv.eventually_forall_dist_lt
    (isCompact_closedBall y _) (fun z hz ↦ (hcl hz).1) (half_pos hε))
  refine ⟨κ / 2, half_pos hκ, (closedBall_subset_ball (half_lt_self hκ)).trans hκT, r₀ / 2,
    half_pos hr₀, fun z hz ↦ (hcl hz).1, N, fun z hz ↦
      ⟨hin (hvK (hcl hz).1) ((mem_ball.1 (hcl hz).2).trans (half_lt_self hε)), fun n hn ↦ ?_⟩⟩
  refine hin (huK _ (hcl hz).1) ((dist_triangle _ (e (v z)) _).trans_lt ?_)
  have h₁ := hNe n hn z hz
  have h₂ := mem_ball.1 (hcl hz).2
  simp only [Function.comp_apply] at h₁ h₂
  linarith

end TauCeti
