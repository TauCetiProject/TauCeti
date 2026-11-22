/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Approximation by ranges of uniformly converging maps

A point frequently approximated by the ranges of a uniformly converging family belongs to
its limiting range closure. A compact continuous limiting map has closed range, so its image
contains every such point. No nontriviality assumption on the indexing filter is needed.
-/

public section

open Set Filter
open scoped Topology

/-- Uniform convergence puts every point frequently approximated by the varying images
in the closure of the limiting image. The domain has no topological assumptions. -/
theorem TendstoUniformly.mem_closure_range_of_approximation
    {A : Type*} {B : Type*} {ι : Type*} [PseudoMetricSpace B]
    {l : Filter ι} {f : ι → A → B} {e : A → B}
    (hlim : TendstoUniformly f e l) {y : B}
    (hnear : ∀ ε > 0, ∃ᶠ k in l, ∃ x, dist (f k x) y < ε) :
    y ∈ closure (range e) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨k, ⟨x, hx⟩, hk⟩ := ((hnear (ε / 2) hhalf).and_eventually
    (Metric.tendstoUniformly_iff.mp hlim (ε / 2) hhalf)).exists
  refine ⟨e x, mem_range_self x, ?_⟩
  calc
    dist y (e x) ≤ dist y (f k x) + dist (f k x) (e x) := dist_triangle _ _ _
    _ = dist (f k x) y + dist (e x) (f k x) := by congr 1 <;> exact dist_comm _ _
    _ < ε := by linarith [hk x]

/-- The compact source image contains every point that is frequently
arbitrarily close to the approximating images. -/
theorem Continuous.mem_range_of_uniform_limit_and_approximation
    {A B ι : Type*} [TopologicalSpace A] [CompactSpace A] [MetricSpace B]
    {l : Filter ι} {f : ι → A → B} {e : A → B}
    (he : Continuous e) (hlim : TendstoUniformly f e l) {y : B}
    (hnear : ∀ ε > 0, ∃ᶠ k in l, ∃ x, dist (f k x) y < ε) : y ∈ range e := by
  simpa only [(isCompact_range he).isClosed.closure_eq] using
    hlim.mem_closure_range_of_approximation hnear
