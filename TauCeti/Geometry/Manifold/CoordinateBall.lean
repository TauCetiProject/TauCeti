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

A coordinate ball about a point `x` of a space charted on a real normed space `E` is an open
embedding of a ball of `E`, or of `E` itself, into the space, sending the centre to `x`.

Let `X` be a Hausdorff space charted on a real normed space `E`. Finitely many points of `X` have
pairwise disjoint coordinate balls about them: for a finite `S ⊆ X` and `r > 0`, there is an open
embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. The proof builds each slice as the
inverse of the chart at `s` precomposed with an affine rescaling, and sends distinct slices into
the disjoint open sets given by `Set.Finite.t2_separation`.

On a manifold without boundary modelled on `E`, through any model with corners `I`, coordinate
balls form a neighbourhood basis: every neighbourhood of `x` contains the range of an open
embedding `E → M` sending `0` to `x`. In particular every point has arbitrarily small open
neighbourhoods homeomorphic to `E`.

## Main results

* `Set.Finite.exists_isOpenEmbedding_prod_ball`: the open embedding of `S × ball 0 r`.
* `TauCeti.exists_isOpenEmbedding_range_subset`: a coordinate ball `E → M` inside a prescribed
  neighbourhood.
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- **Coordinate balls form a neighbourhood basis.** On a space charted on `H` through a model `I`
without boundary, every neighbourhood `s` of a point `x` contains the range of an open embedding
`e : E → M` with `e 0 = x`. -/
theorem exists_isOpenEmbedding_range_subset (I : ModelWithCorners ℝ E H) [I.Boundaryless] {x : M}
    {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ range e ⊆ s := by
  -- The chart at `x`, read in `E` and restricted to the interior of `s`.
  let c := ((chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph).restrOpen (interior s)
    isOpen_interior
  have hx : x ∈ c.source := by
    simp [c, mem_interior_iff_mem_nhds.2 hs]
  obtain ⟨r, hr, hball⟩ := isOpen_iff.mp c.open_target (c x) (c.map_source hx)
  -- A homeomorphism of `E` onto a ball about `c x` inside the chart target.
  let b := OpenPartialHomeomorph.univBall (c x) r
  have hb (v : E) : b v ∈ c.target := hball <| by
    rw [← OpenPartialHomeomorph.univBall_target (c x) hr]
    exact b.map_source (by simp [b])
  let φ := b.trans c.symm
  have hφ : φ.source = univ := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.symm_source, univ_inter]
    exact eq_univ_of_forall hb
  refine ⟨φ, ?_, φ.isOpenEmbedding hφ, ?_⟩
  · simp [φ, b, c.left_inv hx]
  · rintro _ ⟨v, rfl⟩
    exact interior_subset (c.map_target (hb v)).2

end TauCeti
