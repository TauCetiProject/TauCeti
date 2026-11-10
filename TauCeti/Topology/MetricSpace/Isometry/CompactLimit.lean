/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact limits of approximate isometries

Uniformly vanishing distortion upgrades pointwise to uniform convergence on a
compact source. Compactness of the target extracts simultaneous isometric chart
limits, preserving cross-chart distances and coverage by approximating images.

Reference: Kleiner–Lott, *Notes on Perelman's papers*, corrected 2013 version,
Theorem 41.2, Case 2.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

noncomputable section

open Set Filter
open scoped Topology

variable {A B ι : Type*} [PseudoMetricSpace A] [MetricSpace B]

/-- Uniformly vanishing distance distortion upgrades pointwise convergence
to uniform convergence when the source is compact. -/
theorem Isometry.tendstoUniformly_of_distortion_and_pointwise [CompactSpace A]
    {l : Filter ι} {f : ι → A → B} {e : A → B} (he : Isometry e)
    (hpoint : ∀ x, Tendsto (fun k ↦ f k x) l (𝓝 (e x)))
    (hdist : TendstoUniformly (fun k ↦ fun q : A × A ↦ dist (f k q.1) (f k q.2))
      (fun q ↦ dist q.1 q.2) l) : TendstoUniformly f e l := by
  rw [Metric.tendstoUniformly_iff] at hdist ⊢
  intro ε hε
  have hsmall : 0 < ε / 5 := by positivity
  obtain ⟨s, _, hs, hcover⟩ :=
    (isCompact_univ : IsCompact (univ : Set A)).finite_cover_balls hsmall
  have hnet : ∀ᶠ k in l, ∀ z ∈ s, dist (e z) (f k z) < ε / 5 := by
    apply hs.eventually_all.mpr
    intro z hz
    have h := (Metric.tendsto_nhds.mp (hpoint z)) (ε / 5) hsmall
    simpa only [dist_comm] using h
  filter_upwards [hnet, hdist (ε / 5) hsmall] with k hk hkd x
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  -- Ball membership is the distance estimate used in the triangle inequality.
  change dist x z < ε / 5 at hxz
  have hpair := hkd (z, x)
  rw [Real.dist_eq] at hpair
  have hupper : dist (f k z) (f k x) < dist z x + ε / 5 := by
    have hh := (abs_lt.mp hpair).1
    linarith
  calc
    dist (e x) (f k x) ≤ dist (e x) (e z) + dist (e z) (f k z) +
        dist (f k z) (f k x) := dist_triangle4 _ _ _ _
    _ < ε := by rw [he.dist_eq, dist_comm z x] at *; linarith [hk z hz]

namespace TauCeti

/-- Compactness constructs one simultaneous isometric limit from actual
pairwise distance convergence, without a supplied embedding. -/
theorem exists_isometric_ultrafilter_limit [CompactSpace B]
    {l : Filter ι} [l.NeBot] (f : ι → A → B)
    (hdist : ∀ x y, Tendsto (fun k ↦ dist (f k x) (f k y)) l (𝓝 (dist x y))) :
    ∃ U : Ultrafilter ι, (U : Filter ι) ≤ l ∧
      ∃ e : A → B, Isometry e ∧ ∀ x, Tendsto (fun k ↦ f k x) (U : Filter ι) (𝓝 (e x)) := by
  obtain ⟨e, _, he⟩ :=
    (isCompact_univ : IsCompact (univ : Set (A → B))).exists_mapClusterPt
      (f := l) (u := f) (by simp)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp he
  have hpoint (x : A) : Tendsto (fun k ↦ f k x) (U : Filter ι) (𝓝 (e x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hlim
  refine ⟨U, hU, e, Isometry.of_dist_eq ?_, hpoint⟩
  intro x y
  exact tendsto_nhds_unique ((hpoint x).dist (hpoint y)) ((hdist x y).mono_left hU)

end TauCeti

/-- The compact source image contains every point that is eventually
arbitrarily close to the approximating images. -/
theorem Continuous.mem_range_of_uniform_limit_and_approximation
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {l : Filter ι} [l.NeBot] {f : ι → A → B} {e : A → B}
    (he : Continuous e) (hlim : TendstoUniformly f e l) {y : B}
    (hnear : ∀ ε > 0, ∀ᶠ k in l, ∃ x, dist (f k x) y < ε) : y ∈ range e := by
  have hclosed := (isCompact_range he).isClosed
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨k, hk, hx⟩ := ((Metric.tendstoUniformly_iff.mp hlim (ε / 2) hhalf).and
    (hnear (ε / 2) hhalf)).exists
  obtain ⟨x, hx⟩ := hx
  refine ⟨e x, mem_range_self x, ?_⟩
  calc
    dist y (e x) ≤ dist y (f k x) + dist (f k x) (e x) := dist_triangle _ _ _
    _ = dist (f k x) y + dist (e x) (f k x) := by congr 1 <;> exact dist_comm _ _
    _ < ε := by linarith [hk x]

namespace TauCeti

/-- Compact-target extraction preserves the relative positions of an entire
family of compact metric charts along one ultrafilter. -/
theorem exists_common_isometric_limits_preserving_cross_distances
    {ι : Type*} {A : ι → Type*} [∀ i, PseudoMetricSpace (A i)] [∀ i, CompactSpace (A i)]
    {B : Type*} [MetricSpace B] [CompactSpace B]
    {κ : Type*} {l : Filter κ} [l.NeBot]
    (f : κ → ∀ i, A i → B) (D : ∀ i j, A i → A j → ℝ)
    (hdiag : ∀ i, TendstoUniformly
      (fun k (z : A i × A i) ↦ dist (f k i z.1) (f k i z.2))
      (fun z ↦ dist z.1 z.2) l)
    (hcross : ∀ i j x y, Tendsto (fun k ↦ dist (f k i x) (f k j y))
      l (𝓝 (D i j x y))) :
    ∃ U : Ultrafilter κ, (U : Filter κ) ≤ l ∧ ∃ e : ∀ i, A i → B,
      (∀ i, Isometry (e i)) ∧
      (∀ i, TendstoUniformly (fun k ↦ f k i) (e i) (U : Filter κ)) ∧
      (∀ i j x y, dist (e i x) (e j y) = D i j x y) ∧
      ∀ i y, (∀ ε > 0, ∀ᶠ k in l, ∃ x, dist (f k i x) y < ε) → y ∈ range (e i) := by
  obtain ⟨e, _, he⟩ :=
    (isCompact_univ : IsCompact (univ : Set (∀ i, A i → B))).exists_mapClusterPt
      (f := l) (u := f) (by simp)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp he
  have hpoint (i : ι) (x : A i) :
      Tendsto (fun k ↦ f k i x) (U : Filter κ) (𝓝 (e i x)) :=
    (continuous_apply x).continuousAt.tendsto.comp
      ((continuous_apply i).continuousAt.tendsto.comp hlim)
  have hisom (i : ι) : Isometry (e i) := by
    apply Isometry.of_dist_eq
    intro x y
    exact tendsto_nhds_unique ((hpoint i x).dist (hpoint i y))
      (((hdiag i).tendsto_at (x, y)).mono_left hU)
  have huniform (i : ι) : TendstoUniformly (fun k ↦ f k i) (e i) (U : Filter κ) := by
    apply (hisom i).tendstoUniformly_of_distortion_and_pointwise (hpoint i)
    rw [Metric.tendstoUniformly_iff]
    exact fun ε hε ↦ hU (Metric.tendstoUniformly_iff.mp (hdiag i) ε hε)
  refine ⟨U, hU, e, hisom, huniform, ?_, ?_⟩
  · intro i j x y
    exact tendsto_nhds_unique ((hpoint i x).dist (hpoint j y)) ((hcross i j x y).mono_left hU)
  · intro i y hy
    exact (hisom i).continuous.mem_range_of_uniform_limit_and_approximation (huniform i)
      (fun ε hε ↦ hU (hy ε hε))

end TauCeti
