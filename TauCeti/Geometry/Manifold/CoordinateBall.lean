/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Coordinate balls

Let `X` be a space charted on a model `H` homeomorphic to a real normed space `E` through a
boundaryless model with corners `I`; for instance a boundaryless manifold, or a space charted on
`E` itself. Every neighbourhood of a point of `X` contains an open neighbourhood of the point
homeomorphic to `E`: there is an open embedding of `E` into `X` sending `0` to the point, with range
in the given neighbourhood. It is the inverse of the chart at the point, read in `E`, precomposed
with a homeomorphism of `E` onto a small ball (`OpenPartialHomeomorph.univBall`).

Let `X` be a Hausdorff space charted on `E`. Finitely many points of `X` have
pairwise disjoint coordinate balls about them: for a finite `S ⊆ X` and `r > 0`, there is an open
embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. The proof builds each slice as the
inverse of the chart at `s` precomposed with an affine rescaling, and sends distinct slices into
the disjoint open sets given by `Set.Finite.t2_separation`.

## Main results

* `TauCeti.exists_isOpenEmbedding_range_subset`: an open embedding of `E` onto a neighbourhood of a
  point inside a given neighbourhood.
* `Set.Finite.exists_isOpenEmbedding_prod_ball`: the open embedding of `S × ball 0 r`.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace X] [ChartedSpace H X]

/-- **Coordinate neighbourhoods homeomorphic to the model.** In a space charted on a boundaryless
model with corners `I` on a real normed space `E`, every neighbourhood `N` of a point `x` contains
the range of an open embedding of `E` sending `0` to `x`. -/
theorem exists_isOpenEmbedding_range_subset (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {x : X} {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ e : E → X, IsOpenEmbedding e ∧ e 0 = x ∧ range e ⊆ N := by
  -- The chart at `x`, read in `E`.
  set c := (chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ c.source := by simp [c]
  -- A ball about `c x` inside the chart target whose points the inverse chart sends into `N`.
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball (c x) r ⊆ c.target ∩ c.symm ⁻¹' interior N :=
    isOpen_iff.1 (c.isOpen_inter_preimage_symm isOpen_interior) _
      ⟨c.map_source hx, by simpa [c.left_inv hx] using mem_interior_iff_mem_nhds.2 hN⟩
  set g := OpenPartialHomeomorph.univBall (c x) r
  have hg (v : E) : g v ∈ c.target ∩ c.symm ⁻¹' interior N := by
    refine hball ?_
    rw [← OpenPartialHomeomorph.univBall_target _ hr]
    exact g.map_source (by simp [g, OpenPartialHomeomorph.univBall_source])
  have hsource : (g.trans c.symm).source = univ := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.symm_source, univ_inter, eq_univ_iff_forall]
    exact fun v ↦ (hg v).1
  refine ⟨g.trans c.symm, (g.trans c.symm).isOpenEmbedding hsource, ?_, ?_⟩
  · simp [g, OpenPartialHomeomorph.univBall_apply_zero, c.left_inv hx]
  · rintro _ ⟨v, rfl⟩
    exact interior_subset (hg v).2

end TauCeti

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
