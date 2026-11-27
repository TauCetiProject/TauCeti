/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Uniform local properties and norm bounds over compact parameter sets

This file records a uniform local boundedness consequence of continuity over a compact family.
Such bounds provide constant dominating functions for compact-parameter integration.
It also gives a norm-ball version of the tube lemma for properties near a compact fiber.

## Main declarations

* `IsCompact.exists_pos_forall_norm_lt`: a property holding near each point of `{0} × K`
  holds on a uniform norm-ball times `K`.
* `IsCompact.exists_eventually_norm_le`: a function continuous at every point of a compact fiber
  is uniformly bounded on nearby fibers, which remain in any open set containing the original
  fiber.
* `IsCompact.exists_pos_forall_norm_sub_le`: a function continuous at the points of the graph of a
  map over a compact set is uniformly continuous there, in the fibre direction.
* `IsCompact.exists_forall_norm_le_of_eventually_eq_zero`: a function continuous on `K × X`, with
  `K` compact, vanishing outside `K × L` for a compact `L ⊆ X`, is bounded on `K × X`.
* `TauCeti.exists_nonneg_forall_notMem_norm_lt`: in a compact space covered by open sets `U` and
  `V`, the coordinates of the points of `U` outside `V` are bounded.
* `TauCeti.eventually_principal_closedBall_prod_cocompact_iff`: a statement holds eventually
  along `𝓟 (closedBall 0 s) ×ˢ cocompact E` exactly when it holds on a region `‖p‖ ≤ s`,
  `‖z‖ ≥ R`.
* `TauCeti.not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop`: a family whose values at
  one point of `S` have norms tending to infinity has images of `S` in no fixed compact set.
* `TauCeti.tendsto_comap_fst_cocompact_of_eq_zero`: a map on `ℝ × X` vanishing for `|s| > R`
  tends to zero as `|s| → ∞`, uniformly in the second coordinate.
-/

public section

open Filter Set
open scoped Topology

variable {X P H : Type*} [TopologicalSpace X] [TopologicalSpace P] [SeminormedAddGroup H]

/-- A property holding near every point of `{0} × K`, with `K` compact, holds uniformly on
the product of a sufficiently small norm-ball about zero with `K`. -/
theorem IsCompact.exists_pos_forall_norm_lt {K : Set P} (hK : IsCompact K)
    {Q : H → P → Prop} (hQ : ∀ y ∈ K, ∀ᶠ z in 𝓝 ((0 : H), y), Q z.1 z.2) :
    ∃ r > 0, ∀ ⦃x : H⦄, ‖x‖ < r → ∀ y ∈ K, Q x y := by
  simpa using Metric.eventually_nhds_iff.1 (hK.eventually_forall_of_forall_eventually hQ)

/-- A function continuous at every point of `{x₀} × K`, with `K` compact, is uniformly bounded
on `{x} × K` for `x` near `x₀`. These nearby fibers also lie in any open set `W` containing
the original fiber. -/
theorem IsCompact.exists_eventually_norm_le {K : Set P} (hK : IsCompact K)
    {W : Set (X × P)} {F : X × P → H} {x₀ : X} (hW : IsOpen W)
    (hF : ∀ y ∈ K, ContinuousAt F (x₀, y)) (hx₀ : ∀ y ∈ K, (x₀, y) ∈ W) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, (x, y) ∈ W ∧ ‖F (x, y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn fun y hy ↦
    ((hF y hy).comp (Continuous.prodMk_right x₀).continuousAt).continuousWithinAt
  refine ⟨C + 1, hK.eventually_forall_of_forall_eventually fun y hy ↦ ?_⟩
  filter_upwards [hW.eventually_mem (hx₀ y hy),
    (hF y hy).norm.eventually_lt_const ((hC y hy).trans_lt (lt_add_one C))] with z hzW hz
  exact ⟨hzW, hz.le⟩

/-- **Uniform continuity at a compact graph.** Let `x : P → E` be continuous on a compact set `K`,
and let `Φ : P × E → G` be continuous at the points `(p, x p)`, `p ∈ K`. For every `ε > 0` there is
`δ > 0` such that `‖Φ (p, y) - Φ (p, x p)‖ ≤ ε` for every `p ∈ K` and every `y` with
`‖y - x p‖ ≤ δ`. -/
theorem IsCompact.exists_pos_forall_norm_sub_le {M E G : Type*} [PseudoMetricSpace M]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup G] {K : Set M} (hK : IsCompact K)
    {x : M → E} (hx : ContinuousOn x K) {Φ : M × E → G}
    (hΦ : ∀ p ∈ K, ContinuousAt Φ (p, x p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ y : E, ‖y - x p‖ ≤ δ → ‖Φ (p, y) - Φ (p, x p)‖ ≤ ε := by
  -- `Φ` is uniformly continuous at the compact graph `{(p, x p) | p ∈ K}`.
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_dist_lt hx hΦ hε
  refine ⟨δ / 2, by positivity, fun p hp y hy ↦ ?_⟩
  rw [← dist_eq_norm]
  exact (h p hp y (by rw [dist_eq_norm]; linarith)).le

/-- A function `Y` continuous on `K × X`, with `K` compact, and vanishing at `(t, x)` for `x`
outside a compact subset of `X`, is bounded on `K × X`. -/
theorem IsCompact.exists_forall_norm_le_of_eventually_eq_zero {K : Set P} (hK : IsCompact K)
    {Y : P × X → H} (hY : ContinuousOn Y (K ×ˢ univ))
    (hYc : ∀ᶠ p in comap Prod.snd (cocompact X), Y p = 0) :
    ∃ C, ∀ t ∈ K, ∀ x, ‖Y (t, x)‖ ≤ C := by
  obtain ⟨s, hs, hsY⟩ := mem_comap.1 hYc
  obtain ⟨L, hL, hLs⟩ := mem_cocompact.1 hs
  obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn
    (hY.mono (prod_mono subset_rfl (subset_univ L)))
  refine ⟨max C 0, fun t ht x ↦ ?_⟩
  by_cases hx : x ∈ L
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · rw [show Y (t, x) = 0 from hsY (hLs hx), norm_zero]
    exact le_max_right _ _

namespace TauCeti

/-- In a compact space covered by open sets `U` and `V`, the points of `U` outside `V` have
bounded coordinates in any homeomorphism `eU : U ≃ₜ H` with a seminormed group. -/
theorem exists_nonneg_forall_notMem_norm_lt [CompactSpace X] {U V : Set X} (hV : IsOpen V)
    (hUV : U ∪ V = univ) (eU : U ≃ₜ H) : ∃ R, 0 ≤ R ∧ ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R := by
  have hK : IsCompact ((↑) ⁻¹' Vᶜ : Set U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun x hx ↦ (eq_univ_iff_forall.1 hUV x).resolve_right hx]
    exact hV.isClosed_compl.isCompact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn eU.continuous.continuousOn
  exact ⟨max C 0 + 1, by positivity, fun x hx ↦ (hC x hx).trans_lt (by linarith [le_max_left C 0])⟩

/-- A statement holds eventually along `𝓟 (closedBall 0 s) ×ˢ cocompact E` exactly when it holds
on a region `‖p‖ ≤ s`, `‖z‖ ≥ R`. -/
theorem eventually_principal_closedBall_prod_cocompact_iff {E : Type*} [SeminormedAddGroup E]
    [ProperSpace E] {s : ℝ} {q : H × E → Prop} :
    (∀ᶠ w in 𝓟 (Metric.closedBall (0 : H) s) ×ˢ cocompact E, q w) ↔
      ∃ R, ∀ w : H × E, ‖w.1‖ ≤ s → R ≤ ‖w.2‖ → q w := by
  constructor
  · intro h
    obtain ⟨pa, hpa, pb, hpb, hq⟩ := eventually_prod_iff.1 h
    obtain ⟨R, -, hR⟩ :=
      hasBasis_cobounded_norm.eventually_iff.mp (Metric.cobounded_eq_cocompact (α := E) ▸ hpb)
    exact ⟨R, fun w hw₁ hw₂ ↦ hq (eventually_principal.1 hpa w.1 (mem_closedBall_zero_iff.2 hw₁))
      (hR (Set.mem_ofPred.mpr hw₂))⟩
  · rintro ⟨R, hR⟩
    exact eventually_prod_iff.2 ⟨fun p ↦ ‖p‖ ≤ s,
      eventually_principal.2 fun p hp ↦ mem_closedBall_zero_iff.1 hp, fun z ↦ R ≤ ‖z‖,
      tendsto_norm_cocompact_atTop.eventually_ge_atTop R, fun hp _ hz ↦ hR (_, _) hp hz⟩

/-- **Unbounded values violate every image bound.** If the norms of the values `u i z` at one point
`z ∈ S` tend to infinity, then no compact set contains the images `u i '' S` for every `i`. -/
theorem not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop {ι α E : Type*}
    [SeminormedAddCommGroup E] {l : Filter ι} [l.NeBot] {u : ι → α → E} {S : Set α} {z : α}
    (hz : z ∈ S) (hu : Tendsto (fun i ↦ ‖u i z‖) l atTop) :
    ¬ ∃ K : Set E, IsCompact K ∧ ∀ i, MapsTo (u i) S K :=
  not_exists_isCompact_forall_mapsTo_of_tendsto_cocompact hz
    ((tendsto_norm_atTop_iff_cobounded.1 hu).mono_right Metric.cobounded_le_cocompact)

/-- A map on `ℝ × X` vanishing for `|s| > R` tends to zero along both ends `|s| → ∞`, uniformly
in the second coordinate. -/
theorem tendsto_comap_fst_cocompact_of_eq_zero {X W : Type*} [Zero W] [TopologicalSpace W]
    {u : ℝ × X → W} {R : ℝ} (hR : ∀ z, R < |z.1| → u z = 0) :
    Tendsto u (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ᶠ z : ℝ × X in comap Prod.fst (cocompact ℝ), R < |z.1| :=
    tendsto_comap.eventually ((tendsto_norm_cocompact_atTop.eventually_gt_atTop R).mono
      fun s hs ↦ by rwa [Real.norm_eq_abs] at hs)
  filter_upwards [hev] with z hz
  exact (hR z hz).symm

end TauCeti
