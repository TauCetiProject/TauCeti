/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.Order.OrderClosed

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
  since the patch makes `U ∩ Ω` open.

If moreover `‖ν‖ = 1` and `γ` is `G`-Lipschitz, a point `z` on or above the graph sees a closed
ball of radius `ε` inside `Ω` at height `2 (G + 1) ε` above it
(`TauCeti.closedBall_add_smul_subset_of_le_inner`), and the segment from a point of the closure
up to that centre stays in the closure
(`TauCeti.exists_closedBall_subset_segment_subset_closure_of_inter_eq`). For a bounded set with
such a patch at every frontier point this gives, by compactness, a uniform interior ball
condition: there are `κ` and `ε₀ > 0` such that every `x ∈ closure Ω` and every `0 < ε ≤ ε₀`
admit a closed ball `B(y, ε) ⊆ Ω` with `‖x - y‖ ≤ κ ε` and the segment `[x, y]` in `closure Ω`
(`TauCeti.exists_closedBall_subset_segment_subset_closure`). Interpolation inequalities on balls
then extend up to the boundary of such a domain.
-/

public section

open Set Filter Topology Metric
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

/-- **A ball above a point of a Lipschitz graph patch.** Let `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}`
with `‖ν‖ = 1` and `γ` `G`-Lipschitz and invariant along `ν`. If `z` lies on or above the graph and
the closed ball of radius `(2 G + 3) ε` about `z` lies in `U`, then the closed ball of radius `ε`
about the point `z + 2 (G + 1) ε ν` lies in `Ω`: over that ball the graph rises by at most `G ε`
above `γ z`, while `⟪·, ν⟫` stays above `⟪z, ν⟫ + (2 G + 1) ε`. -/
theorem closedBall_add_smul_subset_of_le_inner (hν : ‖ν‖ = 1) {G : ℝ≥0}
    (hγ : LipschitzWith G γ) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) {z : E} (hz : γ z ≤ ⟪z, ν⟫_ℝ) {ε : ℝ}
    (hε : 0 < ε) (hU : closedBall z ((2 * G + 3) * ε) ⊆ U) :
    closedBall (z + (2 * (G + 1) * ε) • ν) ε ⊆ Ω := by
  set y := z + (2 * (G + 1) * ε) • ν
  have hG : (0 : ℝ) ≤ G := G.coe_nonneg
  have hyz : dist y z = 2 * (G + 1) * ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one, Real.norm_of_nonneg (by
      positivity)]
  intro w hw
  rw [mem_closedBall] at hw
  have hwU : w ∈ U := hU (by
    rw [mem_closedBall]
    linarith [dist_triangle w y z])
  -- Over the ball the graph rises by at most `G ε`, and `⟪·, ν⟫` drops by at most `ε`.
  have hγw : γ w ≤ γ z + G * ε := by
    have h := hγ.dist_le_mul w y
    rw [Real.dist_eq, hγν] at h
    nlinarith [le_abs_self (γ w - γ z)]
  have hinner : ⟪y, ν⟫_ℝ - ε ≤ ⟪w, ν⟫_ℝ := by
    have h := abs_real_inner_le_norm (y - w) ν
    rw [hν, mul_one, ← dist_eq_norm, dist_comm, inner_sub_left] at h
    linarith [le_abs_self (⟪y, ν⟫_ℝ - ⟪w, ν⟫_ℝ)]
  have hy : ⟪y, ν⟫_ℝ = ⟪z, ν⟫_ℝ + 2 * (G + 1) * ε := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
    ring
  have hmem : w ∈ U ∩ Ω := by
    rw [hΩ]
    refine ⟨hwU, ?_⟩
    rw [mem_ofPred_eq]
    nlinarith
  exact hmem.2

/-- **A ball above a point of the closure, in a Lipschitz graph patch.** Let
`U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `‖ν‖ = 1` and `γ` `G`-Lipschitz and
invariant along `ν`. If `x ∈ closure Ω` and the closed ball of radius `(2 G + 3) ε` about `x` lies
in `U`, then there is a closed ball `B(y, ε) ⊆ Ω` with `‖x - y‖ = 2 (G + 1) ε` and the segment
`[x, y]` contained in `closure Ω`: take `y = x + 2 (G + 1) ε ν`. -/
theorem exists_closedBall_subset_segment_subset_closure_of_inter_eq (hU : IsOpen U)
    (hν : ‖ν‖ = 1) {G : ℝ≥0} (hγ : LipschitzWith G γ) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) {x : E} (hx : x ∈ closure Ω) {ε : ℝ} (hε : 0 < ε)
    (hxU : closedBall x ((2 * G + 3) * ε) ⊆ U) :
    ∃ y, closedBall y ε ⊆ Ω ∧ segment ℝ x y ⊆ closure Ω ∧ dist x y = 2 * (G + 1) * ε := by
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)
  have hcl := Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner hU hν0
    hγ.continuous.continuousOn hγν hΩ)
  have hxle : γ x ≤ ⟪x, ν⟫_ℝ :=
    ((hcl x).1 ⟨hxU (mem_closedBall_self (by positivity)), hx⟩).2
  set y := x + (2 * (G + 1) * ε) • ν
  have hxy : dist x y = 2 * (G + 1) * ε := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
      Real.norm_of_nonneg (by positivity)]
  refine ⟨y, closedBall_add_smul_subset_of_le_inner hν hγ hγν hΩ hxle hε hxU, fun w hw => ?_,
    hxy⟩
  -- The segment stays in the ball about `x`, on or above the graph.
  have hwx : dist w x ≤ dist x y := (convex_closedBall x (dist x y)).segment_subset
    (mem_closedBall_self dist_nonneg) (by rw [mem_closedBall, dist_comm]) hw
  obtain ⟨θ, ⟨hθ0, -⟩, rfl⟩ := (segment_eq_image' ℝ x y ▸ hw :)
  refine ((hcl _).2 ⟨hxU (by rw [mem_closedBall]; linarith), ?_⟩).2
  beta_reduce
  rw [mem_ofPred_eq, add_sub_cancel_left, smul_smul, hγν, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hν]
  nlinarith [mul_nonneg hθ0 (by positivity : (0 : ℝ) ≤ 2 * (G + 1) * ε)]

/-- **A uniform interior ball condition.** Let `Ω` be a bounded subset of a finite-dimensional
(more generally, proper) real inner product space such that near each frontier point `x`,
`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0` and a
Lipschitz function `γ` invariant along `ν`. Then there are `κ` and `ε₀ > 0` such that for every
`x ∈ closure Ω` and every `0 < ε ≤ ε₀` there is a closed ball `B(y, ε) ⊆ Ω` with `‖x - y‖ ≤ κ ε`
and the segment `[x, y]` contained in `closure Ω`. -/
theorem exists_closedBall_subset_segment_subset_closure [ProperSpace E]
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzWith G γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    (hΩ : Bornology.IsBounded Ω) :
    ∃ κ ε₀ : ℝ, 0 < ε₀ ∧ ∀ x ∈ closure Ω, ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∃ y, closedBall y ε ⊆ Ω ∧ segment ℝ x y ⊆ closure Ω ∧ dist x y ≤ κ * ε := by
  choose! ν γ G r hν hγ hγν hr hpatch using hbdry
  -- Finitely many half-size patch balls cover the compact frontier.
  obtain ⟨t, htfr, hcov⟩ := (hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier
    frontier_subset_closure).elim_nhds_subcover (fun x => ball x (r x / 2))
      fun x hx => ball_mem_nhds x (half_pos (hr x hx))
  -- The rest of `closure Ω` is a compact subset of the interior of `Ω`.
  set K₀ : Set E := closure Ω \ ⋃ x ∈ t, ball x (r x / 2)
  have hK₀Ω : K₀ ⊆ interior Ω := fun z hz => by
    by_contra hzΩ
    exact hz.2 (hcov ⟨hz.1, hzΩ⟩)
  obtain ⟨δ, hδ, hδΩ⟩ := (hΩ.isCompact_closure.diff
    (isOpen_biUnion fun x _ => isOpen_ball)).exists_cthickening_subset_open isOpen_interior hK₀Ω
  -- The scale `ε₀`: at most `δ`, and small enough for every patch.
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ δ ∧ ∀ x ∈ t, ε ≤ r x / (2 * (2 * G x + 3)) :=
    eventually_nhdsWithin_of_eventually_nhds ((eventually_le_nhds hδ).and
      ((eventually_all_finset t).2 fun x hx => eventually_le_nhds (by
        have := hr x (htfr x hx)
        positivity)))
  obtain ⟨ε₀, ⟨hε₀δ, hε₀r⟩, hε₀⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨∑ x ∈ t, 2 * (G x + 1), ε₀, hε₀, fun x hx ε hε hεε₀ => ?_⟩
  by_cases hxt : x ∈ ⋃ i ∈ t, ball i (r i / 2)
  · -- Near the frontier, go up along `ν` inside a patch.
    obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.1 hxt
    have hfr := htfr i hit
    have hεr : (2 * G i + 3) * ε ≤ r i / 2 := by
      have h := (hεε₀.trans (hε₀r i hit))
      rw [le_div_iff₀ (by have := hr i hfr; positivity)] at h
      linarith
    obtain ⟨y, hy, hseg, hxy⟩ := exists_closedBall_subset_segment_subset_closure_of_inter_eq
      isOpen_ball (hν i hfr) (hγ i hfr) (hγν i hfr) (hpatch i hfr) hx hε fun w hw => by
        rw [mem_closedBall] at hw
        rw [mem_ball] at hxi ⊢
        linarith [dist_triangle w x i]
    refine ⟨y, hy, hseg, ?_⟩
    rw [hxy]
    gcongr
    exact Finset.single_le_sum (f := fun x => 2 * ((G x : ℝ) + 1)) (fun j _ => by positivity) hit
  · -- Away from the frontier, `x` is the centre of a ball in the interior of `Ω`.
    refine ⟨x, ((closedBall_subset_cthickening (E := K₀) ⟨hx, hxt⟩ ε).trans
      ((cthickening_mono (hεε₀.trans hε₀δ) K₀).trans hδΩ)).trans interior_subset, ?_, ?_⟩
    · rw [segment_same]
      exact singleton_subset_iff.2 hx
    · rw [dist_self]
      exact mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) hε.le

end TauCeti
