/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Coordinate balls

Let `X` be a space charted on a boundaryless model with real normed vector space `E`. Every point
of `X` has an open neighbourhood homeomorphic to `E`: the inverse chart image of a small ball in
the chart target, which is homeomorphic to the whole of `E` by `OpenPartialHomeomorph.univBall`.

If `X` is Hausdorff and charted on `E` itself, finitely many points of `X` have
pairwise disjoint coordinate balls about them: for a finite `S ⊆ X` and `r > 0`, there is an open
embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. The proof builds each slice as the
inverse of the chart at `s` precomposed with an affine rescaling, and sends distinct slices into
the disjoint open sets given by `Set.Finite.t2_separation`.

## Main results

* `TauCeti.exists_isOpen_mem_homeomorph`: every point has an open neighbourhood homeomorphic to
  `E`.
* `Set.Finite.exists_isOpenEmbedding_prod_ball`: the open embedding of `S × ball 0 r`.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace X] [ChartedSpace H X]

/-- **Coordinate balls.** Every point `x` of a space charted on a boundaryless model `I` with
vector space `E` has an open neighbourhood homeomorphic to `E`. -/
theorem exists_isOpen_mem_homeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (U ≃ₜ E) := by
  -- The chart at `x` followed by the model, an open partial homeomorphism onto an open set of `E`.
  let c : OpenPartialHomeomorph X E := (chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ c.source := by simp [c, mem_chart_source]
  obtain ⟨r, hr, hball⟩ := isOpen_iff.1 c.open_target (c x) (c.map_source hx)
  refine ⟨c.symm '' ball (c x) r, c.isOpen_image_symm_of_subset_target isOpen_ball hball,
    ⟨c x, mem_ball_self hr, c.left_inv hx⟩, ⟨?_⟩⟩
  -- The inverse chart identifies the ball with its image, and `univBall` the ball with `E`.
  exact (c.symm.homeomorphOfImageSubsetSource (by rwa [c.symm_source]) rfl).symm.trans
    ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target (c x) hr).symm).trans
      ((OpenPartialHomeomorph.univBall (c x) r).toHomeomorphSourceTarget.symm.trans
        ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source (c x) r)).trans
          (Homeomorph.Set.univ E))))

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
