/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Isometric approximation in varying ambient spaces

Comparison maps whose images approach the images of source maps under isometric ambient
embeddings inherit convergence of pairwise distances. The pointwise analogue transfers
convergence to a fixed target point. The source and ambient spaces may vary with the index;
compactness, Hausdorff-distance bounds and chart-limit extraction are not required.

These estimates apply to common-ambient realizations of pointed metric approximations.

Reference: Kleiner–Lott, *Notes on Perelman's papers*, corrected 2013 version,
Theorem 41.2, Case 2.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Metric
open scoped Topology

namespace TauCeti

/-- Uniformly close comparison maps in isometrically embedded ambient spaces inherit uniform
convergence of pairwise distances from the source maps. Both the source and ambient spaces
may depend on the filter index. -/
theorem tendstoUniformly_dist_of_ambient_approximation
    {A : Type*} {B : Type*} {ι : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    {X : ι → Type*} {Z : ι → Type*}
    [∀ k, PseudoMetricSpace (X k)] [∀ k, PseudoMetricSpace (Z k)]
    {i : ∀ k, X k → Z k} {j : ∀ k, B → Z k}
    (hi : ∀ k, Isometry (i k)) (hj : ∀ k, Isometry (j k))
    {Φ : ∀ k, A → X k} {ψ : ι → A → B} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0))
    (hψ : ∀ᶠ k in l, ∀ x, dist (i k (Φ k x)) (j k (ψ k x)) < ε k)
    (hΦ : TendstoUniformly (fun k (q : A × A) ↦ dist (Φ k q.1) (Φ k q.2))
      (fun q ↦ dist q.1 q.2) l) :
    TendstoUniformly (fun k (q : A × A) ↦ dist (ψ k q.1) (ψ k q.2))
      (fun q ↦ dist q.1 q.2) l := by
  rw [Metric.tendstoUniformly_iff] at hΦ ⊢
  intro η hη
  have hηfourth : 0 < η / 4 := by positivity
  filter_upwards [hψ, hε.eventually_lt_const hηfourth,
    hΦ (η / 2) (by positivity)] with k hk hεk hΦk q
  have hdist := dist_dist_dist_le (i k (Φ k q.1)) (i k (Φ k q.2))
    (j k (ψ k q.1)) (j k (ψ k q.2))
  rw [(hi k).dist_eq, (hj k).dist_eq] at hdist
  have htriangle := dist_triangle (dist q.1 q.2) (dist (Φ k q.1) (Φ k q.2))
    (dist (ψ k q.1) (ψ k q.2))
  have hsource := hΦk q
  simp only [Real.dist_eq] at hdist htriangle hsource ⊢
  linarith [hk q.1, hk q.2]

/-- If points in varying ambient spaces approach the embedded image of a fixed target point,
then target points approximating them with vanishing error converge to that target point.
Only the target embeddings are required to be isometries. -/
theorem tendsto_of_ambient_approximation
    {B : Type*} {ι : Type*} [PseudoMetricSpace B]
    {Z : ι → Type*} [∀ k, PseudoMetricSpace (Z k)]
    {j : ∀ k, B → Z k} (hj : ∀ k, Isometry (j k))
    {x : ∀ k, Z k} {y : ι → B} {p : B} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0))
    (hy : ∀ᶠ k in l, dist (x k) (j k (y k)) < ε k)
    (hp : Tendsto (fun k ↦ dist (x k) (j k p)) l (𝓝 0)) :
    Tendsto y l (𝓝 p) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _
    (by simpa using hε.add hp)
  filter_upwards [hy] with k hk
  calc
    dist (y k) p = dist (j k (y k)) (j k p) := ((hj k).dist_eq _ _).symm
    _ ≤ dist (j k (y k)) (x k) + dist (x k) (j k p) := dist_triangle _ _ _
    _ ≤ ε k + dist (x k) (j k p) := by rw [dist_comm (j k (y k))]; linarith

end TauCeti
