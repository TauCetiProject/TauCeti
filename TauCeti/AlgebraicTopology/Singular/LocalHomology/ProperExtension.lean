/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.Homotopy.Affine
import TauCeti.Analysis.Normed.Module.Ball.Radial.ProperExtension
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Topology.Maps.Proper.Metric
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Proper radial extensions preserving local index and local surjectivity

Let `E` and `F` be finite-dimensional real normed spaces of the same dimension `n`, oriented by
homological orientations `o` and `o'` (`TauCeti.HomologicalOrientation`). If `f : E → F` is a
continuous map for which `x` is the only solution of `f z = f x` in the ball of radius `r` about
`x`, and `f` stays at distance at least `δ > 0` from `f x` on the sphere of radius `r`, then the
proper radial extension (`ContinuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub`) yields
a proper map `g : E → F` agreeing with `f` on the closed ball whose global degree equals the local
index of `f` at `x`
(`TauCeti.HomologicalOrientation.exists_isProperMap_eqOn_localIndex_eq_degree`).

Two consequences follow:

* **Local surjectivity at a point of nonzero local index.** If `o.localIndex o' f x ≠ 0`, then `f`
  carries every neighbourhood of `x` to a neighbourhood of `f x`
  (`TauCeti.HomologicalOrientation.image_mem_nhds_of_localIndex_ne_zero`).
* **Perturbation by a small linear term.** For a self-map `f : E → E` and a small real scalar `ε`
  with `|ε| * r < δ`, the straight-line homotopy between the proper extension `g` and its radial
  perturbation `g + ε • ρ(· - x)` keeps the fibre over `f x` inside `I × closedBall x r`, so the
  perturbed map is proper, agrees with `f + ε • (· - x)` on the closed ball, and still has degree
  equal to the local index of `f` at `x`
  (`TauCeti.HomologicalOrientation.exists_isProperMap_localIndex_eq_degree`).

## Main results

* `TauCeti.HomologicalOrientation.exists_isProperMap_eqOn_localIndex_eq_degree`: proper radial
  extension from an isolating closed ball whose degree equals the local index.
* `TauCeti.HomologicalOrientation.image_mem_nhds_of_localIndex_ne_zero`: a map with nonzero local
  index at `x` maps every neighbourhood of `x` to a neighbourhood of `f x`.
* `TauCeti.HomologicalOrientation.exists_isProperMap_localIndex_eq_degree`: proper radial
  extension of `f + ε • (· - x)` preserving the local index as global degree.
-/

public section

noncomputable section

open Filter Metric Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

section DifferentSpaces

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}
  (o : HomologicalOrientation E E n) (o' : HomologicalOrientation F F n)

/-- If `x` is the only solution of `f z = f x` in the ball of radius `r` about `x`, and `f` stays
at distance at least `δ > 0` from `f x` on the sphere of radius `r`, then `f` agrees on the closed
ball with a proper map `g` which stays at distance at least `δ` from `f x` outside the open ball,
whose fibre over each value `y` within `δ` of `f x` is the set of solutions of `f z = y` in the
open ball, and the local index of `f` at `x` is the degree of `g`. -/
theorem exists_isProperMap_eqOn_localIndex_eq_degree (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    {f : C(E, F)} {x : E} {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖) (hiso : ∀ z ∈ ball x r, f z = f x → z = x) :
    ∃ g : C(E, F), IsProperMap g ∧ EqOn g f (closedBall x r) ∧
      (∀ z, r ≤ dist z x → δ ≤ ‖g z - f x‖) ∧
      (∀ y, ‖y - f x‖ < δ → g ⁻¹' {y} = {z ∈ ball x r | f z = y}) ∧
      o.localIndex o' f x = o.degree o' hE g := by
  have hrpos : 0 < r := hr.lt_of_ne' fun h ↦ (hfδ x (by simp [h])).not_gt (by simpa using hδ)
  obtain ⟨g, hgp, hgf, hgout⟩ :=
    f.continuous.continuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub hr hδ hfδ
  -- Outside the open ball `g` stays at distance at least `δ` from `f x`, so its fibre over a value
  -- `y` within `δ` of `f x` is the set of solutions in the open ball.
  have hgfib (y : F) (hy : ‖y - f x‖ < δ) : g ⁻¹' {y} = {z ∈ ball x r | f z = y} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hgf (ball_subset_closedBall hz.1)).trans hz.2⟩
    have hzb : z ∈ ball x r := mem_ball.2 (not_le.1 fun h ↦ (hgout z h).not_gt (hz ▸ hy))
    exact ⟨hzb, (hgf (ball_subset_closedBall hzb)).symm.trans hz⟩
  refine ⟨g, hgp, hgf, hgout, hgfib, ?_⟩
  -- `x` is the only preimage of `f x` under `g`, so the local index is the degree.
  have hfib₀ : g ⁻¹' {f x} = {x} := by
    rw [hgfib (f x) (by rwa [sub_self, norm_zero])]
    ext z
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hz ↦ hiso z hz.1 hz.2, by rintro rfl; exact ⟨mem_ball_self hrpos, rfl⟩⟩
  have hgf_nhds : g =ᶠ[𝓝 x] f :=
    eventually_of_mem (ball_mem_nhds x hrpos) fun _ hw ↦ hgf (ball_subset_closedBall hw)
  rw [o.localIndex_congr o' hF hgf_nhds.symm, ← o.localDegree_eq_localIndex o' hE hF g hfib₀,
    o.localDegree_eq_degree o' hE hF hgp]

/-- **Local surjectivity at a point of nonzero local index.** A continuous map `f : E → F` with
nonzero local index at `x` carries every neighbourhood of `x` to a neighbourhood of `f x`. -/
theorem image_mem_nhds_of_localIndex_ne_zero (hF : finrank ℝ F = n) {f : C(E, F)} {x : E}
    (hf : o.localIndex o' f x ≠ 0) {U : Set E} (hU : U ∈ 𝓝 x) : f '' U ∈ 𝓝 (f x) := by
  have hE : finrank ℝ E = n := by_contra fun hne ↦
    hf (o.localIndex_eq_zero_of_finrank_ne o' hne hF f x)
  have hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
    by_contra h
    exact hf (o.localIndex_of_frequently_eq o' f (by simpa using not_eventually.1 h))
  obtain ⟨r, hr, δ, hδ, hrU, hfδ, hiso'⟩ :=
    f.continuous.continuousOn.exists_closedBall_subset_and_le_dist hU hiso
  obtain ⟨g, hgp, -, -, hgfib, hidx⟩ := o.exists_isProperMap_eqOn_localIndex_eq_degree o' hE hF
    hr.le hδ (fun z hz ↦ dist_eq_norm (f z) (f x) ▸ hfδ z hz)
    fun z hz ↦ hiso' z (ball_subset_closedBall hz)
  refine mem_of_superset (ball_mem_nhds (f x) hδ) fun y hy ↦ ?_
  obtain ⟨z, hz⟩ := o.surjective_of_degree_ne_zero o' hE hF hgp (hidx ▸ hf) y
  have hmem : z ∈ g ⁻¹' {y} := hz
  rw [hgfib y (by rwa [← dist_eq_norm])] at hmem
  exact ⟨z, hrU (ball_subset_closedBall hmem.1), hmem.2⟩

end DifferentSpaces

section SelfMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (o o' : HomologicalOrientation E E n)

/-- Near a point `x` which is the only solution of `f z = f x` in the ball of radius `r`, with `f`
at distance at least `δ` from `f x` on the sphere of radius `r`, the map `f` and the map
`f + ε • (· - x)`, for `|ε| * r < δ`, are related by a proper homotopy: there is a proper map `G`
whose degree is the local index of `f` at `x`, equal to `f + ε • (· - x)` on the closed ball, and
at distance at least `δ - |ε| * r` from `f x` outside the open ball. -/
theorem exists_isProperMap_localIndex_eq_degree (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    {r δ ε : ℝ} (hr : 0 ≤ r) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) (hε : |ε| * r < δ) :
    ∃ G : C(E, E), IsProperMap G ∧ o.localIndex o' f x = o.degree o' hE G ∧
      EqOn G (fun z ↦ f z + ε • (z - x)) (closedBall x r) ∧
      ∀ z, r ≤ dist z x → δ - |ε| * r ≤ ‖G z - f x‖ := by
  obtain ⟨g, hgp, hgf, hgout, -, hidx⟩ := o.exists_isProperMap_eqOn_localIndex_eq_degree o' hE hE hr
    ((mul_nonneg (abs_nonneg ε) hr).trans_lt hε) hfδ hiso
  let G : C(E, E) :=
    ⟨fun z ↦ g z + ε • radialRetraction r (z - x),
      g.continuous.add
        (((lipschitzWith_radialRetraction hr).continuous.comp
          (continuous_id.sub continuous_const)).const_smul ε)⟩
  have hdist (z : E) : dist (g z) (G z) ≤ |ε| * r := by
    rw [dist_comm, dist_eq_norm]
    simp only [G, ContinuousMap.coe_mk, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simp [norm_radialRetraction hr]) (abs_nonneg ε)
  have hGp : IsProperMap G := hgp.of_dist_le G.continuous hdist
  -- The straight-line homotopy from `g` to `G` has a compact fibre over `f x`, inside `I × B`.
  let H := ContinuousMap.Homotopy.affine g G
  have hHc : IsCompact (H ⁻¹' {f x}) := by
    refine (isCompact_univ.prod (isCompact_closedBall x r)).of_isClosed_subset
      (isClosed_singleton.preimage H.continuous) fun p hp ↦ ⟨mem_univ _, ?_⟩
    by_contra hpB
    have h1 : δ ≤ dist (g p.2) (f x) := by
      rw [dist_eq_norm]
      exact hgout p.2 (not_le.1 (mem_closedBall.not.1 hpB)).le
    have h2 : dist (H p) (g p.2) ≤ |ε| * r := by
      have ht : ‖(p.1 : ℝ)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg p.1.property.1]
        exact p.1.property.2
      simpa only [H, ContinuousMap.Homotopy.affine_apply, dist_lineMap_left] using
        (mul_le_of_le_one_left dist_nonneg ht).trans (hdist p.2)
    rw [mem_singleton_iff.1 hp, dist_comm] at h2
    linarith
  refine ⟨G, hGp, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hidx, ← o.localDegree_eq_degree o' hE hE hgp (f x),
      o.localDegree_eq_of_homotopy_of_isCompact o' hE hE H hHc,
      o.localDegree_eq_degree o' hE hE hGp]
  · simp only [G, ContinuousMap.coe_mk, hgf hz,
      radialRetraction_of_norm_le (by simpa [dist_eq_norm] using hz : ‖z - x‖ ≤ r)]
  · have h3 := dist_triangle (g z) (G z) (f x)
    rw [dist_eq_norm (g z), dist_eq_norm (G z)] at h3
    linarith [hgout z hz, hdist z]

end SelfMap

end HomologicalOrientation

end TauCeti
