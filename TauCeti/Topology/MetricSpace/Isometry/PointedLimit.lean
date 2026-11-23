/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.MetricSpace.Isometry.AmbientApproximation
public import TauCeti.Topology.MetricSpace.Isometry.CompactLimit
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Topology.MetricSpace.PartialEquiv

/-!
# Chart limits in pointed Hausdorff approximations

Isometric embeddings into common ambient spaces realize pointed metric approximations.
Hausdorff proximity constructs comparison maps from compact source charts, rather than
assuming a relation or its surjectivity. A limiting isometric chart covers the corresponding
ball when the source charts cover those balls. The ambient spaces and source spaces may vary.

Reference: Kleiner–Lott, *Notes on Perelman's papers*, corrected 2013 version,
Theorem 41.2, Case 2.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace TauCeti

/-- Common ambient realizations of Hausdorff-close source sets and a compact target construct
comparison maps and a pointed isometric chart limit. Source-ball coverage passes to that limit.
No relation, comparison map, limiting embedding, or target-ball coverage is supplied as input. -/
theorem exists_isometric_limit_covering_ball_of_hausdorffEDist
    {A : Type*} {B : Type*} {ι : Type*}
    [PseudoMetricSpace A] [CompactSpace A] [MetricSpace B] [CompactSpace B]
    {X : ι → Type*} {Z : ι → Type*}
    [∀ k, PseudoMetricSpace (X k)] [∀ k, PseudoMetricSpace (Z k)]
    {i : ∀ k, X k → Z k} {j : ∀ k, B → Z k}
    (hi : ∀ k, Isometry (i k)) (hj : ∀ k, Isometry (j k))
    {D : ∀ k, Set (X k)} {Φ : ∀ k, A → X k} {o : A} {p : B} {r : ℝ}
    {l : Filter ι} [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝 0))
    (hGH : ∀ᶠ k in l, hausdorffEDist (i k '' D k) (range (j k)) < ENNReal.ofReal (ε k))
    (himage : ∀ᶠ k in l, ∀ x, Φ k x ∈ D k)
    (hΦ : TendstoUniformly (fun k (q : A × A) ↦ dist (Φ k q.1) (Φ k q.2))
      (fun q ↦ dist q.1 q.2) l)
    (hp : Tendsto (fun k ↦ dist (i k (Φ k o)) (j k p)) l (𝓝 0))
    (hchart : ∀ᶠ k in l, ball (Φ k o) r ⊆ range (Φ k)) :
    ∃ ψ : ι → A → B,
      (∀ᶠ k in l, ∀ x, dist (i k (Φ k x)) (j k (ψ k x)) < ε k) ∧
      ∃ U : Ultrafilter ι, (U : Filter ι) ≤ l ∧ ∃ e : A → B,
        Isometry e ∧ TendstoUniformly ψ e (U : Filter ι) ∧ e o = p ∧
          ball p r ⊆ range e := by
  classical
  have hselect : ∀ᶠ k in l, ∃ ψ : A → B,
      ∀ x, dist (i k (Φ k x)) (j k (ψ x)) < ε k := by
    filter_upwards [hGH, himage] with k hk hki
    have hnear (x : A) : ∃ y : B, dist (i k (Φ k x)) (j k y) < ε k := by
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
        exists_edist_lt_of_hausdorffEDist_lt (mem_image_of_mem _ (hki x)) hk
      exact ⟨y, edist_lt_ofReal.mp hy⟩
    exact ⟨fun x ↦ (hnear x).choose, fun x ↦ (hnear x).choose_spec⟩
  obtain ⟨ψ, hψ⟩ := hselect.choice
  have hdist := tendstoUniformly_dist_of_ambient_approximation hi hj hε hψ hΦ
  obtain ⟨U, hU, e, he, hpoint⟩ := exists_isometric_ultrafilter_limit ψ
    (fun x y ↦ hdist.tendsto_at (x, y))
  have hlim := he.tendstoUniformly_of_distortion_and_pointwise hpoint (fun u hu ↦ hU (hdist u hu))
  have hcenter : e o = p := tendsto_nhds_unique (hpoint o)
    ((tendsto_of_ambient_approximation hj hε (hψ.mono fun _ hk ↦ hk o) hp).mono_left hU)
  refine ⟨ψ, hψ, U, hU, e, he, hlim, hcenter, ?_⟩
  rw [← hcenter]
  have htwice : Tendsto (fun k ↦ 2 * ε k) (U : Filter ι) (𝓝 0) := by
    simpa using (hε.const_mul 2).mono_left hU
  apply he.continuous.ball_subset_range_of_uniform_relation_approximation
    (R := fun k x y ↦ dist (i k x) (j k y) ≤ ε k) hlim
    htwice (hU (hψ.mono fun _ hk x ↦ (hk x).le))
  · exact hU (Eventually.of_forall fun k x y z w hx hy ↦ by
      have h := dist_dist_dist_le (i k x) (i k y) (j k z) (j k w)
      rw [(hi k).dist_eq, (hj k).dist_eq, Real.dist_eq] at h
      linarith)
  · intro y _
    have hGU : ∀ᶠ k in (U : Filter ι),
        hausdorffEDist (i k '' D k) (range (j k)) < ENNReal.ofReal (ε k) := hU hGH
    apply hGU.frequently.mono
    intro k hk
    obtain ⟨_, ⟨x, _, rfl⟩, hx⟩ := exists_edist_lt_of_hausdorffEDist_lt
      (mem_range_self y) (by simpa only [hausdorffEDist_comm] using hk)
    exact ⟨x, by simpa only [dist_comm] using (edist_lt_ofReal.mp hx).le⟩
  · exact hU hchart

/-- Radial source charts and common-ambient pointed approximations identify a whole ball
in the metric limit with the compact coordinate chart. The chart maps, comparison maps, and
limiting isometric embedding are constructed on the native closed-ball subtypes.
Smooth normal charts may be supplied through their underlying partial equivalences. -/
theorem exists_isometric_closedBall_limit_of_pointed_hausdorffEDist
    {E : Type*} {B : Type*} {ι : Type*}
    [PseudoMetricSpace E] [MetricSpace B]
    {X : ι → Type*} {Z : ι → Type*}
    [∀ k, PseudoMetricSpace (X k)] [∀ k, PseudoMetricSpace (Z k)]
    {i : ∀ k, X k → Z k} {j : ∀ k, B → Z k}
    (hi : ∀ k, Isometry (i k)) (hj : ∀ k, Isometry (j k))
    (Φ : ∀ k, PartialEquiv E (X k)) {a : E} {q : ∀ k, X k} {p : B}
    {r S : ℝ} (hr : 0 ≤ r) (hrS : r ≤ S)
    (hA : IsCompact (closedBall a r)) (hB : IsCompact (closedBall p S))
    {l : Filter ι} [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝 0))
    (hGH : ∀ᶠ k in l, hausdorffEDist (i k '' closedBall (q k) S)
      (j k '' closedBall p S) < ENNReal.ofReal (ε k))
    (hsource : ∀ᶠ k in l, closedBall a r ⊆ (Φ k).source)
    (htarget : ∀ᶠ k in l, ball (q k) r ⊆ (Φ k).target)
    (hradial : ∀ᶠ k in l, ∀ x ∈ (Φ k).source, dist (Φ k x) (q k) = dist x a)
    (hΦ : TendstoUniformly
      (fun k (z : closedBall a r × closedBall a r) ↦ dist (Φ k z.1) (Φ k z.2))
      (fun z ↦ dist z.1 z.2) l)
    (hp : Tendsto (fun k ↦ dist (i k (Φ k a)) (j k p)) l (𝓝 0)) :
    ∃ ψ : ι → closedBall a r → B,
      (∀ᶠ k in l, ∀ x : closedBall a r, dist (i k (Φ k x)) (j k (ψ k x)) < ε k) ∧
      ∃ U : Ultrafilter ι, (U : Filter ι) ≤ l ∧
        ∃ e : closedBall a r → B, Isometry e ∧ TendstoUniformly ψ e (U : Filter ι) ∧
          e ⟨a, mem_closedBall_self hr⟩ = p ∧ ball p r ⊆ range e := by
  let A := closedBall a r
  let K := closedBall p S
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have : CompactSpace K := isCompact_iff_compactSpace.mp hB
  let o : A := ⟨a, mem_closedBall_self hr⟩
  let p' : K := ⟨p, mem_closedBall_self (hr.trans hrS)⟩
  let j' (k : ι) : K → Z k := fun y ↦ j k y
  have hcontrol : ∀ᶠ k in l,
      (∀ x : A, Φ k x ∈ closedBall (q k) S) ∧
        ball (Φ k a) r ⊆ range (fun x : A ↦ Φ k x) := by
    filter_upwards [hsource, htarget, hradial] with k hks hkt hkr
    constructor
    · intro x
      exact closedBall_subset_closedBall hrS
        ((Φ k).mapsTo_closedBall_of_dist_eq hks hkr x.property)
    · intro y hy
      have hcenter : dist (Φ k a) (q k) = 0 := by
        simpa using hkr a (hks (mem_closedBall_self hr))
      have hyq : y ∈ ball (q k) r := by
        rw [Metric.mem_ball, ← dist_congr_left hcenter]
        exact Metric.mem_ball.mp hy
      obtain ⟨x, hx, hxy⟩ := (Φ k).ball_subset_image_closedBall_of_dist_eq hkt hkr hyq
      exact ⟨⟨x, hx⟩, hxy⟩
  have hGH' : ∀ᶠ k in l, hausdorffEDist (i k '' closedBall (q k) S)
      (range (j' k)) < ENNReal.ofReal (ε k) := by
    simpa only [j', ← Function.comp_def, range_comp, Subtype.range_coe] using hGH
  obtain ⟨ψ, hψ, U, hU, e, he, hlim, hcenter, hcover⟩ :=
    exists_isometric_limit_covering_ball_of_hausdorffEDist hi
      (fun k ↦ (hj k).comp isometry_subtypeVal) (o := o) (p := p') hε hGH'
      (hcontrol.mono fun _ hk ↦ hk.1) hΦ hp (hcontrol.mono fun _ hk ↦ hk.2)
  refine ⟨fun k x ↦ (ψ k x : B), hψ, U, hU, fun x ↦ (e x : B),
    isometry_subtypeVal.comp he, ?_, congrArg Subtype.val hcenter, ?_⟩
  · rw [Metric.tendstoUniformly_iff] at hlim ⊢
    exact hlim
  · intro y hy
    have hyK : y ∈ K := closedBall_subset_closedBall hrS (ball_subset_closedBall hy)
    have hyball : (⟨y, hyK⟩ : K) ∈ ball p' r := by
      rw [← Subtype.preimage_ball]
      exact hy
    obtain ⟨x, hx⟩ := hcover hyball
    exact ⟨x, congrArg Subtype.val hx⟩

end TauCeti
