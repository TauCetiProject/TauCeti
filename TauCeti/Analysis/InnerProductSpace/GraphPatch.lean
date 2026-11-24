/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The closure and frontier of a domain inside a graph patch

Let `ν ≠ 0` be a vector of a real inner product space and `γ` a function invariant under translation
along `ν`. The region `{z | γ z < ⟪z, ν⟫}` lies above the graph `{z | ⟪z, ν⟫ = γ z}` of a function
over the hyperplane `ν^⊥`. A domain `Ω` has a *graph patch* on an open set `U` when

`U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}`,

which is how a domain with `C^k` boundary is described near a boundary point. Inside such a patch:

* every point on or above the graph lies in the closure of `Ω`
  (`TauCeti.inter_setOf_le_inner_subset_closure`); no regularity of `γ` is needed, since such a
  point `y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it;
* if `γ` is continuous on `U`, the closure of `Ω` is the closed region `{z | γ z ≤ ⟪z, ν⟫}`
  (`TauCeti.inter_closure_eq_inter_setOf_le_inner`), and the frontier of `Ω` is the graph
  `{z | ⟪z, ν⟫ = γ z}` (`TauCeti.inter_frontier_eq_inter_setOf_inner_eq`); `Ω` need not be open,
  since the patch makes `U ∩ Ω` open;
* if `‖ν‖ = 1` and `γ` is `G`-Lipschitz, every segment from a point `x` on or above the graph to a
  point `x + ε ν + e` with `(1 + G) ‖e‖ ≤ ε` that stays in `U` lies in the closure of `Ω`
  (`TauCeti.segment_add_smul_add_subset_closure`): the graph rises by at most `G t ‖e‖` along
  the segment, while `⟪·, ν⟫` rises by at least `t (ε - ‖e‖)`. So a point of the closure sees a
  ball about `x + ε ν` through `closure Ω`
  (`TauCeti.exists_forall_segment_subset_closure_of_ball_subset`).

A bounded set `Ω` of a proper space with a Lipschitz graph patch at every frontier point therefore
satisfies a *uniform cone condition* (`TauCeti.exists_forall_segment_subset_closure`): there are an
aperture `θ ∈ (0, 1]` and a scale `ε₀ > 0` such that for every `ε ≤ ε₀`, every point `x` of
`closure Ω` has a point `p` within `ε` of it with all segments from `x` to the closed ball of
radius `θ ε` about `p` inside `closure Ω`. Interpolation inequalities up to the boundary use this
to reach a point of the boundary from inside the domain.
-/

public section

open Set Filter Topology
open scoped InnerProductSpace NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {U Ω : Set E} {ν : E}
  {γ : E → ℝ}

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` invariant
along `ν ≠ 0`, every point on or above the graph of `γ` lies in the closure of `Ω`: such a point
`y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it. -/
theorem inter_setOf_le_inner_subset_closure (hU : IsOpen U) (hν : ν ≠ 0)
    (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z) (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} ⊆ closure Ω := by
  rintro y ⟨hy, hle : γ y ≤ ⟪y, ν⟫_ℝ⟩
  -- Approach `y` along `ν` from above.
  have ht : Tendsto (fun t : ℝ => y + t • ν) (𝓝[>] 0) (𝓝 y) := by
    have h0 : Tendsto (fun t : ℝ => y + t • ν) (𝓝 0) (𝓝 (y + (0 : ℝ) • ν)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht (hU.mem_nhds hy), self_mem_nhdsWithin] with t htU htpos
  have hmem : y + t • ν ∈ U ∩ Ω := by
    rw [hΩ]
    refine ⟨htU, ?_⟩
    rw [mem_ofPred_eq, hγν, inner_add_left, real_inner_smul_left]
    have hνν : 0 < ⟪ν, ν⟫_ℝ := real_inner_self_pos.2 hν
    have ht0 : (0 : ℝ) < t := htpos
    linarith [mul_pos ht0 hνν]
  exact hmem.2

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the closure of `Ω` is the closed region on or above the graph
of `γ`. -/
theorem inter_closure_eq_inter_setOf_le_inner (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ closure Ω = U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} :=
  Subset.antisymm
    (fun _ hy => ⟨hy.1, inter_closure_subset_setOf_le hU hγ
      (continuous_id.inner continuous_const).continuousOn hΩ hy⟩)
    (fun _ hy => ⟨hy.1, inter_setOf_le_inner_subset_closure hU hν hγν hΩ hy⟩)

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the frontier of `Ω` is the graph of `γ`. -/
theorem inter_frontier_eq_inter_setOf_inner_eq (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ frontier Ω = U ∩ {z | ⟪z, ν⟫_ℝ = γ z} := by
  have hcl := Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner hU hν hγ hγν hΩ)
  -- The patch makes `U ∩ Ω` open, so its points are interior points of `Ω`.
  have hUΩ : IsOpen (U ∩ Ω) := by
    have hf : ContinuousOn (fun z => ⟪z, ν⟫_ℝ - γ z) U :=
      (continuous_id.inner continuous_const).continuousOn.sub hγ
    have := hf.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
    rwa [hΩ, show {z | γ z < ⟪z, ν⟫_ℝ} = (fun z => ⟪z, ν⟫_ℝ - γ z) ⁻¹' Ioi 0 by
      ext; simp [sub_pos]]
  ext y
  constructor
  · rintro ⟨hy, hycl, hynΩ⟩
    have hle : γ y ≤ ⟪y, ν⟫_ℝ := ((hcl y).1 ⟨hy, hycl⟩).2
    -- A point of `U` strictly above the graph lies in the interior of `Ω`.
    refine ⟨hy, le_antisymm (not_lt.1 fun hlt => hynΩ ?_) hle⟩
    have hyΩ : y ∈ U ∩ Ω := hΩ ▸ ⟨hy, hlt⟩
    exact interior_maximal inter_subset_right hUΩ hyΩ
  · rintro ⟨hy, heq⟩
    refine ⟨hy, ((hcl y).2 ⟨hy, heq.ge⟩).2, fun hyΩ => ?_⟩
    -- A point of `U ∩ Ω` lies strictly above the graph.
    exact (((Set.ext_iff.1 hΩ y).1 ⟨hy, interior_subset hyΩ⟩).2 : γ y < ⟪y, ν⟫_ℝ).ne heq.symm

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `‖ν‖ = 1` and
`γ` `G`-Lipschitz and invariant along `ν`, a segment from a point `x` on or above the graph to
`x + ε ν + e`, with `(1 + G) ‖e‖ ≤ ε`, lies in the closure of `Ω` as soon as it lies in `U`. -/
theorem segment_add_smul_add_subset_closure (hU : IsOpen U) (hν : ‖ν‖ = 1) {G : ℝ≥0}
    (hγ : LipschitzWith G γ) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) {x e : E} {ε : ℝ} (hx : γ x ≤ ⟪x, ν⟫_ℝ)
    (he : (1 + G) * ‖e‖ ≤ ε) (hseg : segment ℝ x (x + ε • ν + e) ⊆ U) :
    segment ℝ x (x + ε • ν + e) ⊆ closure Ω := by
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)
  intro y hy
  refine inter_setOf_le_inner_subset_closure hU hν0 hγν hΩ ⟨hseg hy, ?_⟩
  rw [segment_eq_image'] at hy
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hy
  -- Along the segment the graph rises by at most `G t ‖e‖`, while `⟪·, ν⟫` rises by at least
  -- `t (ε - ‖e‖)`.
  have hsplit : x + t • (x + ε • ν + e - x) = (x + t • e) + (t * ε) • ν := by module
  have hγle : γ (x + t • e) ≤ γ x + G * (t * ‖e‖) := by
    have := hγ.dist_le_mul (x + t • e) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      at this
    linarith [le_abs_self (γ (x + t • e) - γ x)]
  have hinner : ⟪x + t • e + (t * ε) • ν, ν⟫_ℝ = ⟪x, ν⟫_ℝ + t * ⟪e, ν⟫_ℝ + t * ε := by
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hν]
    ring
  have heν : -‖e‖ ≤ ⟪e, ν⟫_ℝ := by
    have := abs_real_inner_le_norm e ν
    rw [hν, mul_one] at this
    linarith [neg_abs_le ⟪e, ν⟫_ℝ]
  simp only [mem_ofPred_eq]
  rw [hsplit, hγν, hinner]
  nlinarith [mul_le_mul_of_nonneg_left he ht0, mul_le_mul_of_nonneg_left heν ht0]

open Metric in
/-- **The cone condition in a graph patch.** Inside a graph patch on `ball x₀ r`, with `‖ν‖ = 1` and
`γ` `G`-Lipschitz and invariant along `ν`, let `x ∈ closure Ω` with `ball x η ⊆ ball x₀ r`. If
`2 ε < η` and `(1 + G) θ ≤ 1`, then the point `p = x + ε ν` satisfies
`dist x p ≤ ε`, and every segment from `x` to a point of `closedBall p (θ ε)` lies in
`closure Ω`. -/
theorem exists_forall_segment_subset_closure_of_ball_subset (hν : ‖ν‖ = 1) {G : ℝ≥0}
    (hγ : LipschitzWith G γ) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z) {x₀ : E} {r : ℝ}
    (hΩ : ball x₀ r ∩ Ω = ball x₀ r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) {x : E} (hx : x ∈ closure Ω)
    {η ε θ : ℝ} (hη : ball x η ⊆ ball x₀ r) (hε : 0 < ε) (hεη : 2 * ε < η)
    (hθG : (1 + G) * θ ≤ 1) :
    ∃ p, dist x p ≤ ε ∧ ∀ z ∈ closedBall p (θ * ε), segment ℝ x z ⊆ closure Ω := by
  have hηpos : 0 < η := by linarith
  have hθ1 : θ ≤ 1 := by
    rcases le_or_gt 0 θ with hθ | hθ
    · nlinarith [G.coe_nonneg]
    · linarith
  refine ⟨x + ε • ν, by simp [norm_smul, hν, abs_of_pos hε], fun z hz => ?_⟩
  have hz' : z = x + ε • ν + (z - (x + ε • ν)) := by abel
  have he : ‖z - (x + ε • ν)‖ ≤ θ * ε := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hGe : (1 + G) * ‖z - (x + ε • ν)‖ ≤ ε := by
    calc (1 + G) * ‖z - (x + ε • ν)‖ ≤ (1 + G) * (θ * ε) := by gcongr
      _ = ((1 + G) * θ) * ε := by ring
      _ ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
  have hzx : dist z x < η := by
    have hpx : dist (x + ε • ν) x = ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one, Real.norm_of_nonneg hε.le]
    nlinarith [dist_triangle z (x + ε • ν) x, mem_closedBall.1 hz]
  have hseg : segment ℝ x z ⊆ ball x₀ r :=
    ((convex_ball x η).segment_subset (mem_ball_self hηpos) (mem_ball.2 hzx)).trans hη
  -- `x` lies in the closure of `Ω` inside the patch, so on or above the graph.
  have hxγ : γ x ≤ ⟪x, ν⟫_ℝ :=
    ((Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner isOpen_ball
      (norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)) hγ.continuous.continuousOn hγν hΩ)
      x).1 ⟨hη (mem_ball_self hηpos), hx⟩).2
  rw [hz'] at hseg ⊢
  exact segment_add_smul_add_subset_closure isOpen_ball hν hγ hγν hΩ hxγ hGe hseg

open Metric in
/-- **The uniform cone condition.** Let `Ω` be a bounded set in a proper real inner product space
with a Lipschitz graph patch at every frontier point `x`: `ball x r ∩ Ω = ball x r ∩
{z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0` and a Lipschitz function `γ` invariant
along `ν`. Then there are `0 < θ ≤ 1` and `ε₀ > 0` such that for every `0 < ε ≤ ε₀`, every
`x ∈ closure Ω` has a point `p` with `dist x p ≤ ε` and every segment from `x` to a point of
`closedBall p (θ ε)` inside `closure Ω`. -/
theorem exists_forall_segment_subset_closure [ProperSpace E] (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzWith G γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ x ∈ closure Ω,
      ∃ p, dist x p ≤ ε ∧ ∀ z ∈ closedBall p (θ * ε), segment ℝ x z ⊆ closure Ω := by
  have hcl : IsCompact (closure Ω) := hΩ.isCompact_closure
  choose! ν γ G r hν hγ hγν hr hpatch using hbdry
  -- Finitely many patch balls cover the compact frontier; with `interior Ω` they cover the
  -- closure, and a Lebesgue number `η` of this cover fixes the scale.
  obtain ⟨t, htfr, hcov⟩ :=
    (hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure).elim_nhds_subcover
      (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  set c : Option t → Set E := fun i => i.elim (interior Ω) fun x => ball (x : E) (r x)
  have hcopen : ∀ i, IsOpen (c i) := by
    rintro (_ | x)
    · exact isOpen_interior
    · exact isOpen_ball
  have hccov : closure Ω ⊆ ⋃ i, c i := fun z hz => by
    by_cases hzi : z ∈ interior Ω
    · exact mem_iUnion.2 ⟨none, hzi⟩
    · obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov ⟨hz, hzi⟩)
      exact mem_iUnion.2 ⟨some ⟨x, hxt⟩, hzx⟩
  obtain ⟨η, hη, hleb⟩ := lebesgue_number_lemma_of_metric hcl hcopen hccov
  -- The aperture `θ = 1 / (1 + ∑ G)` serves every patch of the finite cover.
  set S : ℝ := ∑ x ∈ t, (G x : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hθ1 : 1 / (1 + S) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  refine ⟨1 / (1 + S), by positivity, hθ1, η / 4, by positivity, fun ε hε hεη x hx => ?_⟩
  obtain ⟨i, hi⟩ := hleb x hx
  rcases i with _ | ⟨x₀, hx₀t⟩
  · -- Near the interior, the ball about `x` itself lies in `Ω`.
    refine ⟨x, by simp [hε.le], fun z hz => ?_⟩
    have hball : closedBall x (1 / (1 + S) * ε) ⊆ interior Ω :=
      (closedBall_subset_ball (by nlinarith [mul_le_of_le_one_left hε.le hθ1])).trans hi
    exact ((convex_closedBall x _).segment_subset (mem_closedBall_self (by positivity)) hz).trans
      (hball.trans (interior_subset.trans subset_closure))
  · -- In a patch, the cone opens along the normal `ν x₀`.
    have hx₀ : x₀ ∈ frontier Ω := htfr x₀ hx₀t
    have hG : (G x₀ : ℝ) ≤ S := Finset.single_le_sum (f := fun x => (G x : ℝ))
      (fun _ _ => NNReal.coe_nonneg _) hx₀t
    refine exists_forall_segment_subset_closure_of_ball_subset (hν x₀ hx₀) (hγ x₀ hx₀)
      (hγν x₀ hx₀) (hpatch x₀ hx₀) hx hi hε (by linarith) ?_
    rw [mul_one_div, div_le_one (by positivity)]
    linarith

end TauCeti
