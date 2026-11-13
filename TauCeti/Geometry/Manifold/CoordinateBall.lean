/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens

/-!
# Coordinate balls in charted spaces

Let `X` be a Hausdorff space charted on a real normed space `E`. Finitely many points of `X` have
pairwise disjoint coordinate balls about them: for a finite `S ⊆ X` and `r > 0`, there is an open
embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. The proof builds each slice as the
inverse of the chart at `s` precomposed with an affine rescaling, and sends distinct slices into
the disjoint open sets given by `Set.Finite.t2_separation`.

A compact space charted on a pseudometric space is covered by finitely many coordinate balls
`(e i).preimageBall (c i) (r i)` of atlas charts, with `closedBall (c i) (K * r i)` in the chart
target for a prescribed factor `K` and its image under `(e i).symm` inside a member of any given
open cover; for `1 ≤ K` the coordinate balls therefore refine that cover. When `X` is
Hausdorff and the model space is proper, `OpenPartialHomeomorph.isCompact_closure_preimageBall`
and `OpenPartialHomeomorph.closure_preimageBall_subset` show that for radii `ρ < σ ≤ K * r i` the
coordinate ball of radius `ρ` has compact closure inside that of radius `σ`. For `K = 3`, the radii
`r i`, `2 * r i` and `3 * r i` give three nested finite covers, each closure compact in the next;
such nested covers carry compact restriction maps between Čech cochain spaces.

## Main results

* `Set.Finite.exists_isOpenEmbedding_prod_ball`: the open embedding of `S × ball 0 r`.
* `TauCeti.exists_finite_preimageBall_cover`: the finite cover by coordinate balls.
-/

public section

open Metric Set Topology

namespace Set.Finite

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [ChartedSpace E X] {S : Set X}

/-- **Disjoint coordinate balls about finitely many points.** For a finite set `S` and `r > 0`,
there is an open embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. -/
theorem exists_isOpenEmbedding_prod_ball (hS : S.Finite) {r : ℝ} (hr : 0 < r) :
    ∃ F : S × ball (0 : E) r → X, IsOpenEmbedding F ∧
      ∀ s, F (s, ⟨0, mem_ball_self hr⟩) = s := by
  have := hS.to_subtype
  obtain ⟨W, hW, hWd⟩ := hS.t2_separation
  -- In the chart at `s`, a ball of radius `ε s` about `s` lies in the target and maps into `W s`.
  have hε (s : S) : ∃ ε > 0, ball (chartAt E (s : X) s) ε ⊆
      (chartAt E (s : X)).target ∩ (chartAt E (s : X)).symm ⁻¹' W s :=
    isOpen_iff.1 ((chartAt E (s : X)).isOpen_inter_preimage_symm (hW s).2) _
      ⟨(chartAt E (s : X)).map_source (mem_chart_source E _), by
        simpa [(chartAt E (s : X)).left_inv (mem_chart_source E _)] using (hW s).1⟩
  choose ε hε₀ hεW using hε
  have hc (s : S) : ε s / r ≠ 0 := (div_pos (hε₀ s) hr).ne'
  -- The rescaling `z ↦ c s + (ε s / r) • z` sends `ball 0 r` into `ball (c s) (ε s)`.
  have hball (s : S) {z : E} (hz : z ∈ ball (0 : E) r) :
      chartAt E (s : X) s + (ε s / r) • z ∈ ball (chartAt E (s : X) s) (ε s) := by
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_self_add_left, norm_smul]
    calc ‖ε s / r‖ * ‖z‖ < ‖ε s / r‖ * r := by gcongr; exact norm_pos_iff.2 (hc s)
      _ = ε s := by rw [Real.norm_of_nonneg (div_pos (hε₀ s) hr).le]; field_simp
  let g (s : S) (z : E) : X := (chartAt E (s : X)).symm (chartAt E (s : X) s + (ε s / r) • z)
  refine ⟨fun p ↦ g p.1 p.2, .of_continuous_injective_isOpenMap
    (continuous_prod_of_discrete_left.2 fun s ↦ ((chartAt E (s : X)).continuousOn_symm.comp
      (by fun_prop) fun z hz ↦ (hεW s (hball s hz)).1).comp_continuous continuous_subtype_val
        fun z ↦ z.2) (fun p q h ↦ ?_) (isOpenMap_prod_of_discrete_left.2 fun s U hU ↦ ?_),
    fun s ↦ by simp [g, (chartAt E (s : X)).left_inv (mem_chart_source E _)]⟩
  · -- The common value lies in `W p.1 ∩ W q.1`, so `p.1 = q.1`; charts are injective.
    obtain ⟨⟨s, hsS⟩, z, hz⟩ := p
    obtain ⟨⟨s', hs'S⟩, z', hz'⟩ := q
    have h₁ : g ⟨s, hsS⟩ z ∈ W s := (hεW ⟨s, hsS⟩ (hball ⟨s, hsS⟩ hz)).2
    have h₂ : g ⟨s', hs'S⟩ z' ∈ W s' := (hεW ⟨s', hs'S⟩ (hball _ hz')).2
    simp only at h
    obtain rfl : s = s' := hWd.elim hsS hs'S <| not_disjoint_iff.2 ⟨_, h₁, h ▸ h₂⟩
    have := (chartAt E s).symm.injOn (hεW ⟨s, hsS⟩ (hball _ hz)).1
      (hεW ⟨s, hsS⟩ (hball _ hz')).1 h
    simpa using smul_right_injective E (hc ⟨s, hsS⟩) (add_left_cancel this)
  · -- On a slice the map is a chart inverse after an affine homeomorphism of `E`.
    rw [← image_image (g s), ← image_image (chartAt E (s : X)).symm]
    exact (chartAt E (s : X)).isOpen_image_symm_of_subset_target
      (((isOpenMap_add_left _).comp (isOpenMap_smul₀ (hc s))) _
        (isOpen_ball.isOpenMap_subtype_val U hU))
      (by rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩; exact (hεW s (hball s z.2)).1)

end Set.Finite

namespace TauCeti

open TopologicalSpace

universe u

variable {H : Type*} {X : Type u} [PseudoMetricSpace H] [TopologicalSpace X] [ChartedSpace H X]

/-- **Finite covers by coordinate balls.** A compact charted space is covered by finitely many
coordinate balls `(e i).preimageBall (c i) (r i)` of atlas charts with
`closedBall (c i) (K * r i) ⊆ (e i).target`, each with `(e i).symm '' closedBall (c i) (K * r i)`
inside a member of the given open cover `V`. -/
theorem exists_finite_preimageBall_cover [CompactSpace X] (K : ℝ) {κ : Type*} {V : κ → Opens X}
    (hV : IsOpenCover V) :
    ∃ (ι : Type u) (_ : Finite ι) (e : ι → OpenPartialHomeomorph X H) (c : ι → H) (r : ι → ℝ),
      (∀ i, e i ∈ atlas H X) ∧ (∀ i, 0 < r i) ∧
        (∀ i, closedBall (c i) (K * r i) ⊆ (e i).target) ∧
          (∀ i, ∃ k, (e i).symm '' closedBall (c i) (K * r i) ⊆ V k) ∧
            ⨆ i, (e i).preimageBall (c i) (r i) = ⊤ := by
  choose k hk using hV.exists_mem
  -- In the chart at `x`, a ball of radius `ε x` lies in the target and maps into `V (k x)`.
  have hε (x : X) : ∃ ε > 0, ball (chartAt H x x) ε ⊆
      (chartAt H x).target ∩ (chartAt H x).symm ⁻¹' V (k x) :=
    isOpen_iff.1 ((chartAt H x).isOpen_inter_preimage_symm (V (k x)).isOpen) _
      ⟨mem_chart_target H x, by simpa [(chartAt H x).left_inv (mem_chart_source H x)] using hk x⟩
  choose ε hε₀ hεV using hε
  -- The radius `ε x / (max K 1 + 1)` keeps `closedBall (K * r)` inside `ball (ε x)`.
  set r : X → ℝ := fun x ↦ ε x / (max K 1 + 1)
  have hr (x : X) : 0 < r x := div_pos (hε₀ x) (by positivity)
  have hKr (x : X) : closedBall (chartAt H x x) (K * r x) ⊆ ball (chartAt H x x) (ε x) := by
    refine closedBall_subset_ball ?_
    have hεr : ε x = (max K 1 + 1) * r x := by
      simp only [r]; field_simp
    nlinarith [le_max_left K 1, hr x]
  let D : X → Opens X := fun x ↦ (chartAt H x).preimageBall (chartAt H x x) (r x)
  have hD : IsOpenCover D := .mk <| eq_top_iff.2 fun x _ ↦
    Opens.mem_iSup.2 ⟨x, OpenPartialHomeomorph.mem_preimageBall.2
      ⟨mem_chart_source H x, mem_ball_self (hr x)⟩⟩
  obtain ⟨s, hs⟩ := hD.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ chartAt H i.1, fun i ↦ chartAt H i.1 i.1, fun i ↦ r i.1,
    fun i ↦ chart_mem_atlas H i.1, fun i ↦ hr i.1,
    fun i ↦ (hKr i.1).trans fun z hz ↦ (hεV i.1 hz).1,
    fun i ↦ ⟨k i.1, by rintro _ ⟨z, hz, rfl⟩; exact (hεV i.1 (hKr i.1 hz)).2⟩, hs.iSup_eq_top⟩

end TauCeti
