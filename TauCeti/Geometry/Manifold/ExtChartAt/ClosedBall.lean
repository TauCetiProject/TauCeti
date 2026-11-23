/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Closed coordinate balls

A closed ball contained in an extended chart target pulls back to a compact subset of the chart
source. Its membership is the closed coordinate-distance inequality, and the corresponding
strict inequality places a point in its interior. No smoothness or Riemannian metric is needed.

Maps into a compact set `K` of a manifold that converge locally uniformly after composing with a
continuous map `e` injective on `K` (for instance an embedding into a vector space) can be read in
a chart: near a point whose limit value lies in the chart source, the limit and the tail of the
sequence take values in a closed coordinate ball inside the chart target. If moreover the maps are
differentiable, the limit is `C¹` and the derivatives of the coordinate expressions converge, the
coordinate expressions converge uniformly near that point together with their derivatives.

## Main results

* `TauCeti.Manifold.chart_closedBall_properties`: compactness, membership and interior criteria.
* `IsCompact.exists_closedBall_forall_mem_extChartAt_source`: maps into a compact set converging
  locally uniformly through a continuous injection are eventually in a closed coordinate ball
  near each point.
* `IsCompact.exists_closedBall_tendstoUniformlyOn_extChartAt_comp`: for such maps converging in
  `C¹` in a chart, the coordinate expressions converge uniformly with their derivatives on a closed
  ball near each point.

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

namespace TauCeti

open Filter Function

variable {E H M G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] [NormedAddCommGroup G] [NormedSpace ℝ G] [ProperSpace G] [MetricSpace F]

/-- **The coordinate expressions converge in `C¹` near a point.** Let `uₙ` and `v` map an open set
`S` of a proper normed space into a compact set `K` of a manifold, with `uₙ → v` locally uniformly
through a map `e` continuous and injective on `K`. Let the `uₙ` be differentiable and `v` be `C¹`,
and let the derivatives of the coordinate expressions in the chart at `v y`, for some `y ∈ S`,
converge locally uniformly where `v` lies in the chart source. Then on a closed disc
`closedBall y r ⊆ S` the limit and the tail `u (n + N)` take values in the source of the chart at
`v y`, and the coordinate expressions of the tail converge uniformly to that of `v`, together with
their derivatives. -/
theorem _root_.IsCompact.exists_closedBall_tendstoUniformlyOn_extChartAt_comp {K : Set M}
    {e : M → F} (hK : IsCompact K) (he : ContinuousOn e K) (he_inj : InjOn e K) {S : Set G}
    (hS : IsOpen S) {u : ℕ → G → M} {v : G → M} (hu : ∀ n, MDifferentiableOn 𝓘(ℝ, G) I (u n) S)
    (huK : ∀ n, MapsTo (u n) S K) (hv : ContMDiffOn 𝓘(ℝ, G) I 1 v S) (hvK : MapsTo v S K)
    (hconv : TendstoLocallyUniformlyOn (fun n ↦ e ∘ u n) (e ∘ v) atTop S) {y : G} (hy : y ∈ S)
    (hdconv : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I (v y) ∘ u n))
      (fderiv ℝ (extChartAt I (v y) ∘ v)) atTop (S ∩ v ⁻¹' (extChartAt I (v y)).source)) :
    ∃ r > 0, ∃ N, closedBall y r ⊆ S ∧
      (∀ z ∈ closedBall y r, v z ∈ (extChartAt I (v y)).source ∧
        ∀ n, u (n + N) z ∈ (extChartAt I (v y)).source) ∧
      ContinuousOn (fun z ↦ (z, (extChartAt I (v y) ∘ v) z,
        fderiv ℝ (extChartAt I (v y) ∘ v) z)) (closedBall y r) ∧
      TendstoUniformlyOn (fun n ↦ extChartAt I (v y) ∘ u (n + N)) (extChartAt I (v y) ∘ v)
        atTop (closedBall y r) ∧
      TendstoUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I (v y) ∘ u (n + N)))
        (fderiv ℝ (extChartAt I (v y) ∘ v)) atTop (closedBall y r) := by
  set χ := extChartAt I (v y)
  -- On a disc `B` about `y`, the limit and the tail `u (n + N)` take values in the chart at `v y`.
  obtain ⟨κ, -, -, r, hr, hcl, N, hN⟩ := hK.exists_closedBall_forall_mem_extChartAt_source he
    he_inj hS huK hv.continuousOn hvK hconv hy (mem_extChartAt_source (I := I) (v y))
  have hBS : ball y r ⊆ S := ball_subset_closedBall.trans hcl
  have hvB {z : G} (hz : z ∈ ball y r) : v z ∈ χ.source :=
    (hN z (ball_subset_closedBall hz)).1.1
  have huB (n : ℕ) {z : G} (hz : z ∈ ball y r) : u (n + N) z ∈ χ.source :=
    ((hN z (ball_subset_closedBall hz)).2 (n + N) (Nat.le_add_left N n)).1
  have hχv : ContDiffOn ℝ 1 (χ ∘ v) (ball y r) :=
    contMDiffOn_iff_contDiffOn.1 <| contMDiffOn_extChartAt.comp (hv.mono hBS) fun z hz ↦ by
      rw [mem_preimage, ← extChartAt_source I]
      exact hvB hz
  have hχu (n : ℕ) {z : G} (hz : z ∈ ball y r) : DifferentiableAt ℝ (χ ∘ u (n + N)) z :=
    mdifferentiableAt_iff_differentiableAt.1 <|
      (mdifferentiableAt_extChartAt (by rw [← extChartAt_source I]; exact huB n hz)).comp z
        ((hu (n + N) z (hBS hz)).mdifferentiableAt (hS.mem_nhds (hBS hz)))
  -- The derivatives converge uniformly on the closed disc of radius `r / 2`.
  have hsub : closedBall y (r / 2) ⊆ ball y r := closedBall_subset_ball (half_lt_self hr)
  have hd : TendstoUniformlyOn (fun n ↦ fderiv ℝ (χ ∘ u (n + N))) (fderiv ℝ (χ ∘ v)) atTop
      (closedBall y (r / 2)) := by
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact
      (hv.continuousOn.isOpen_inter_preimage hS (isOpen_extChartAt_source (v y)))).1
      hdconv _ (fun z hz ↦ ⟨hBS (hsub hz), hvB (hsub hz)⟩) (isCompact_closedBall _ _)
    rw [← map_add_atTop_eq_nat N] at h
    exact TauCeti.tendstoUniformlyOn_map_iff.1 h
  -- The maps converge pointwise in `M`, as `e` is a homeomorphism from `K` onto its image.
  have hpt {z : G} (hz : z ∈ S) : Tendsto (fun n ↦ u n z) atTop (𝓝 (v z)) :=
    hK.tendsto_nhds_of_tendsto_comp he he_inj (.of_forall fun n ↦ huK n hz) (hvK hz)
      (hconv.tendsto_at hz)
  -- The coordinate expressions converge pointwise, hence uniformly on the disc of radius `r / 2`.
  have hptB {z : G} (hz : z ∈ ball y r) :
      Tendsto (fun n ↦ (χ ∘ u (n + N)) z) atTop (𝓝 ((χ ∘ v) z)) :=
    (continuousAt_extChartAt' (hvB hz)).tendsto.comp
      ((hpt (hBS hz)).comp (tendsto_add_atTop_nat N))
  have hc : TendstoUniformlyOn (fun n ↦ χ ∘ u (n + N)) (χ ∘ v) atTop (ball y (r / 2)) :=
    (uniformCauchySeqOn_ball_of_fderiv (hd.mono ball_subset_closedBall).uniformCauchySeqOn
      (fun n z hz ↦ (hχu n (ball_subset_ball (half_le_self hr.le) hz)).hasFDerivAt)
      (hptB (mem_ball_self hr)).cauchy_map).tendstoUniformlyOn_of_tendsto
      fun z hz ↦ hptB (ball_subset_ball (half_le_self hr.le) hz)
  have hC : closedBall y (r / 4) ⊆ ball y (r / 2) := closedBall_subset_ball (by linarith)
  refine ⟨r / 4, by positivity, N, (hC.trans (ball_subset_ball (half_le_self hr.le))).trans hBS,
    fun z hz ↦ ⟨hvB (hsub (closedBall_subset_closedBall (by linarith) hz)),
      fun n ↦ huB n (hsub (closedBall_subset_closedBall (by linarith) hz))⟩,
    (continuousOn_id.prodMk (hχv.continuousOn.prodMk
      (hχv.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl))).mono
      (hC.trans (ball_subset_ball (half_le_self hr.le))),
    hc.mono hC, hd.mono (hC.trans ball_subset_closedBall)⟩

end TauCeti
