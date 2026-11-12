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

The same chart, read through a linear identification with a real normed space `E` of the right
dimension and rescaled, places a compact set missing `p` inside the image of the open unit ball of
`E` under a continuous injection of `E` which misses `p`
(`TauCeti.exists_continuous_injective_subset_image_ball`).

## Main results

* `TauCeti.exists_continuousOn_injOn_mapsTo_sphere`: a map of the sphere, continuous and injective
  off a point `p`, which is the identity near `y` and pushes a compact set missing `p` into a given
  neighbourhood of `y`.
* `TauCeti.exists_continuous_injective_subset_image_ball`: a compact set missing a point `x₀` of
  the sphere lies in the image of the open unit ball under a continuous injection missing `x₀`.

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
  have hsymm : IsOpenEmbedding φ.symm := φ.symm.isOpenEmbedding htgt
  set c := φ y
  -- `K` is bounded in the chart, and `φ.symm` maps a closed ball around `c` into `N`.
  have hKφ : K ⊆ φ.source := fun z hz ↦ by rw [hsrc]; exact fun h ↦ hpK (h ▸ hz)
  obtain ⟨R, hR⟩ :=
    (hK.image_of_continuousOn (φ.continuousOn.mono hKφ)).isBounded.subset_closedBall c
  have hNc : φ.symm ⁻¹' N ∈ 𝓝 c :=
    hsymm.continuous.continuousAt.preimage_mem_nhds (by rwa [φ.left_inv hyφ])
  obtain ⟨δ, hδ, hδN⟩ := nhds_basis_closedBall.mem_iff.1 hNc
  -- A radial squeeze about `c`, fixing `closedBall c (δ / 2)`.
  obtain ⟨ρ, hρfix, hρmaps⟩ := exists_homeomorph_eqOn_closedBall_mapsTo_closedBall
    (E := EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) (r := R) (half_pos hδ).le (half_lt_self hδ)
  refine ⟨fun z ↦ φ.symm (ρ (φ z - c) + c), ?_, fun z hz z' hz' h ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · exact hsymm.continuous.comp_continuousOn (((ρ.continuous.comp_continuousOn
      (φ.continuousOn.sub continuousOn_const)).add continuousOn_const).mono hsrc.symm.subset)
  · exact φ.injOn (hsrc ▸ hz) (hsrc ▸ hz')
      (sub_left_injective (ρ.injective (add_left_injective c (hsymm.injective h))))
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A compact subset of a sphere lies in a cell.** Let `K` be a compact subset of the unit sphere
`Sⁿ` of a real inner product space of dimension `n + 1`, missing a point `x₀`, and let `E` be a
real normed space of dimension `n`. There is a continuous injection `ψ` of `E` into the sphere,
missing `x₀`, which maps the open unit ball onto a set containing `K`: the inverse of the
stereographic chart from `x₀`, read through a linear identification of `E` with Euclidean space
and rescaled. -/
theorem exists_continuous_injective_subset_image_ball
    (hEF : finrank ℝ F = finrank ℝ E + 1) {x₀ : sphere (0 : F) 1} {K : Set (sphere (0 : F) 1)}
    (hK : IsCompact K) (hx₀ : x₀ ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ x₀ ∉ range ψ ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) x₀
  have hsrc : φ.source = {x₀}ᶜ := stereographic'_source x₀
  have htgt : φ.target = univ := stereographic'_target x₀
  have hsymm : IsOpenEmbedding φ.symm := φ.symm.isOpenEmbedding htgt
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hKs : K ⊆ φ.source := fun x hx ↦ by
    rw [hsrc]
    exact fun h ↦ hx₀ (h ▸ hx)
  -- `K` is bounded in the chart; rescale by some `R` beyond the bound.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x ↦ L.symm (φ x)) (L.symm.continuous.comp_continuousOn (φ.continuousOn.mono hKs))
  obtain ⟨R, hR, hCR⟩ : ∃ R : ℝ, 0 < R ∧ C < R :=
    ⟨max C 0 + 1, by positivity, by linarith [le_max_left C 0]⟩
  refine ⟨fun z ↦ φ.symm (L (R • z)), hsymm.continuous.comp (L.continuous.comp
    (continuous_const_smul R)), fun z z' h ↦ smul_right_injective E hR.ne'
    (L.injective (hsymm.injective h)), ?_, fun x hx ↦ ⟨R⁻¹ • L.symm (φ x), ?_, ?_⟩⟩
  · rintro ⟨z, hz⟩
    have := φ.map_target (x := L (R • z)) (htgt ▸ mem_univ _)
    rw [show φ.symm (L (R • z)) = x₀ from hz, hsrc] at this
    exact this rfl
  · simpa [norm_smul, abs_of_pos hR, inv_mul_lt_one₀ hR] using (hC x hx).trans_lt hCR
  · simp only [smul_inv_smul₀ hR.ne', ContinuousLinearEquiv.apply_symm_apply]
    exact φ.left_inv (hKs hx)

end TauCeti
