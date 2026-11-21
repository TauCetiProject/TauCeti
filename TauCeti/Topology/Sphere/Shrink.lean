/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Radial.OrderIso

/-!
# Pushing a compact subset of a sphere towards a point

Let `K` be a compact subset of the unit sphere of a finite-dimensional real inner product space,
missing a point `p`, and let `N` be a neighbourhood of a point `y ≠ p`. Reading the complement of
`p` in the stereographic chart from `p`, a radial squeeze about the image of `y`
(`TauCeti.exists_homeomorph_eqOn_closedBall_mapsTo_closedBall`) gives a map of the sphere,
continuous and injective off `p`, which is the identity near `y` and carries `K` into `N`. This is
the replacement for the homeomorphism `h` in M. Brown's proof of the generalized Schoenflies
theorem.

## Main results

* `TauCeti.exists_continuousOn_injOn_mapsTo_sphere`: a map of the sphere, continuous and injective
  off a point `p`, which is the identity near `y` and pushes a compact set missing `p` into a given
  neighbourhood of `y`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Pushing a compact subset of a sphere towards a point.** Let `K` be a compact subset of the
unit sphere of a finite-dimensional real inner product space, missing a point `p`, and let `N` be a
neighbourhood of a point `y ≠ p`. There is a map `k` of the sphere, continuous and injective on the
complement of `p`, which is the identity near `y` and maps `K` into `N`. -/
theorem exists_continuousOn_injOn_mapsTo_sphere [FiniteDimensional ℝ F] {p y : sphere (0 : F) 1}
    (hyp : y ≠ p) {K N : Set (sphere (0 : F) 1)} (hK : IsCompact K) (hpK : p ∉ K) (hN : N ∈ 𝓝 y) :
    ∃ k : sphere (0 : F) 1 → sphere (0 : F) 1, ContinuousOn k {p}ᶜ ∧ InjOn k {p}ᶜ ∧
      k =ᶠ[𝓝 y] id ∧ MapsTo k K N := by
  have : Nontrivial F := ⟨⟨y, 0, ne_zero_of_mem_unit_sphere y⟩⟩
  have : Fact (finrank ℝ F = finrank ℝ F - 1 + 1) :=
    ⟨by have := finrank_pos (R := ℝ) (M := F); omega⟩
  -- Work in the stereographic chart `φ` from `p`, defined on `{p}ᶜ` with target the whole space.
  set φ := stereographic' (finrank ℝ F - 1) p
  have hsrc : φ.source = {p}ᶜ := stereographic'_source p
  have htgt : φ.target = univ := stereographic'_target p
  have hyφ : y ∈ φ.source := by rw [hsrc]; exact hyp
  have hsymm : Continuous φ.symm := continuousOn_univ.1 (htgt ▸ φ.continuousOn_symm)
  set c := φ y
  -- `K` is bounded in the chart, and `φ.symm` maps a closed ball around `c` into `N`.
  have hKφ : K ⊆ φ.source := fun z hz ↦ by rw [hsrc]; exact fun h ↦ hpK (h ▸ hz)
  obtain ⟨R, hR⟩ :=
    (hK.image_of_continuousOn (φ.continuousOn.mono hKφ)).isBounded.subset_closedBall c
  have hNc : φ.symm ⁻¹' N ∈ 𝓝 c :=
    hsymm.continuousAt.preimage_mem_nhds (by rwa [φ.left_inv hyφ])
  obtain ⟨δ, hδ, hδN⟩ := nhds_basis_closedBall.mem_iff.1 hNc
  -- A radial squeeze about `c`, fixing `closedBall c (δ / 2)`.
  obtain ⟨ρ, hρfix, hρmaps⟩ := exists_homeomorph_eqOn_closedBall_mapsTo_closedBall
    (E := EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) (r := R) (half_pos hδ).le (half_lt_self hδ)
  refine ⟨fun z ↦ φ.symm (ρ (φ z - c) + c), ?_, fun z hz z' hz' h ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · exact hsymm.comp_continuousOn (((ρ.continuous.comp_continuousOn
      (φ.continuousOn.sub continuousOn_const)).add continuousOn_const).mono hsrc.symm.subset)
  · have h' := φ.symm.injOn (by rw [φ.symm_source, htgt]; trivial)
      (by rw [φ.symm_source, htgt]; trivial) h
    exact φ.injOn (hsrc ▸ hz) (hsrc ▸ hz')
      (sub_left_injective (ρ.injective (add_left_injective c h')))
  · filter_upwards [φ.open_source.mem_nhds hyφ,
      φ.continuousAt hyφ |>.preimage_mem_nhds (ball_mem_nhds c (half_pos hδ))] with z hz hzc
    have hzc' : φ z - c ∈ closedBall 0 (δ / 2) := by
      rw [mem_closedBall_zero_iff, ← dist_eq_norm]
      exact (mem_ball.1 hzc).le
    rw [hρfix hzc', id, sub_add_cancel, φ.left_inv hz, id]
  · refine hδN (mem_closedBall_iff_norm.2 ?_)
    rw [add_sub_cancel_right, ← mem_closedBall_zero_iff]
    exact hρmaps <|
      mem_closedBall_zero_iff.2 (mem_closedBall_iff_norm.1 (hR (mem_image_of_mem φ hz)))

end TauCeti
