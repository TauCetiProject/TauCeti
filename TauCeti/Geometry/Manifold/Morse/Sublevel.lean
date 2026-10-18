/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.NormalizedChart
public import TauCeti.Topology.Order.Sublevel
import Mathlib.Topology.Connected.Clopen
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Disc sublevels at nondegenerate extrema

Near a nondegenerate minimum, small closed sublevels are closed Euclidean discs. Near a
nondegenerate maximum the analogous statement holds for superlevels. The homeomorphisms
retain the value of the function as the squared radial coordinate; for positive radii the
endpoint level corresponds to the boundary sphere.

For a unique global minimum, one compact sublevel strictly above the minimum suffices to make
this a description of the whole small sublevel, not just its intersection with a chart.
No properness, global Morse condition, metric on the manifold, or compactness of the manifold
is required. All statements include zero-dimensional manifolds.

The local construction uses the normalized Morse charts of
`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 2 and 3.
-/

public section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {x : M}

variable [IsManifold I ∞ M]

/-- A neighbourhood of a nondegenerate critical point of index zero has small closed sublevels
homeomorphic to closed Euclidean discs. The function is its minimum value plus the squared
radial coordinate. The radius-zero case is included. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_local_sublevel_homeomorph_closedBall
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hidx : manifoldMorseIndex I f x = 0) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ R > 0, ∀ r, 0 ≤ r → r < R →
      ∃ e : {y : M // y ∈ U ∧ f y ≤ f x + r ^ 2} ≃ₜ
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ∀ y : {y : M // y ∈ U ∧ f y ≤ f x + r ^ 2},
          f y = f x + ‖(e y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ 2 := by
  obtain ⟨ψ, hxψ, hψx, hψ⟩ := h.exists_normalized_morseChart hf
  have hnorm (y : M) (hy : y ∈ ψ.source) : f y = f x + ‖ψ y‖ ^ 2 := by
    simpa [hidx, EuclideanSpace.real_norm_sq_eq] using hψ y hy
  have hzero : (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∈ ψ.target := by
    rw [← hψx]
    exact ψ.toOpenPartialHomeomorph.map_source hxψ
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (ψ.open_target.mem_nhds hzero)
  refine ⟨ψ.source, ψ.open_source, hxψ, R, hR, fun r hr hrR ↦ ?_⟩
  have himage : ψ '' {y | y ∈ ψ.source ∧ f y ≤ f x + r ^ 2} =
      Metric.closedBall 0 r := by
    ext v
    constructor
    · rintro ⟨y, ⟨hy, hfy⟩, rfl⟩
      have hs : ‖ψ y‖ ^ 2 ≤ r ^ 2 := by rw [hnorm y hy] at hfy; linarith
      simpa [Metric.mem_closedBall, dist_zero_right] using (sq_le_sq₀ (norm_nonneg _) hr).mp hs
    · intro hv
      have hvt : v ∈ ψ.target := hball (Metric.closedBall_subset_ball hrR hv)
      refine ⟨ψ.toOpenPartialHomeomorph.symm v,
        ⟨ψ.toOpenPartialHomeomorph.symm.map_source hvt, ?_⟩,
        ψ.toOpenPartialHomeomorph.right_inv hvt⟩
      have hcancel : ψ (ψ.toOpenPartialHomeomorph.symm v) = v :=
        ψ.toOpenPartialHomeomorph.right_inv hvt
      rw [hnorm _ (ψ.toOpenPartialHomeomorph.symm.map_source hvt), hcancel]
      have hvnorm : ‖v‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hv
      exact add_le_add le_rfl ((sq_le_sq₀ (norm_nonneg _) hr).mpr hvnorm)
  let e := ψ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
    (s := {y | y ∈ ψ.source ∧ f y ≤ f x + r ^ 2}) (fun y hy ↦ hy.1) himage
  -- This restriction homeomorphism applies the original chart to the underlying point.
  exact ⟨e, fun y ↦ hnorm y y.property.1⟩

/-- On a Hausdorff manifold, the component of a sufficiently small sublevel containing a
nondegenerate index-zero critical point is a closed Euclidean disc. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_sublevel_component_homeomorph_closedBall
    [T2Space M] (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hidx : manifoldMorseIndex I f x = 0) :
    ∃ R > 0, ∀ r, 0 ≤ r → r < R →
      Nonempty (↥(connectedComponentIn {y | f y ≤ f x + r ^ 2} x) ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r) := by
  obtain ⟨U, hU, hxU, R, hR, he⟩ := h.exists_local_sublevel_homeomorph_closedBall hf hidx
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  obtain ⟨e, -⟩ := he r hr hrR
  let B := {y | f y ≤ f x + r ^ 2}
  let S := {y | y ∈ U ∧ f y ≤ f x + r ^ 2}
  let : CompactSpace S := e.symm.compactSpace
  have hSc : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hSp : IsPreconnected S := by
    let : PreconnectedSpace (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_closedBall _ _).isPreconnected
    let : PreconnectedSpace S :=
      e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hxB : x ∈ B := by dsimp [B]; nlinarith [sq_nonneg r]
  have hxS : x ∈ S := ⟨hxU, hxB⟩
  let V : Set B := Subtype.val ⁻¹' U
  have hV : IsClopen V := by
    refine ⟨?_, hU.preimage continuous_subtype_val⟩
    have hv : V = Subtype.val ⁻¹' S := by
      ext y
      exact ⟨fun hy ↦ ⟨hy, y.property⟩, And.left⟩
    rw [hv]
    exact hSc.isClosed.preimage continuous_subtype_val
  have hCV : connectedComponent (⟨x, hxB⟩ : B) ⊆ V :=
    isPreconnected_connectedComponent.subset_isClopen hV ⟨⟨x, hxB⟩, mem_connectedComponent, hxU⟩
  have hset : connectedComponentIn B x = S := by
    refine subset_antisymm ?_ (hSp.subset_connectedComponentIn hxS (fun y hy ↦ hy.2))
    rw [connectedComponentIn_eq_image hxB]
    rintro y ⟨z, hz, rfl⟩
    exact ⟨hCV hz, z.property⟩
  exact ⟨(Homeomorph.setCongr hset).trans e⟩

/-- Near a nondegenerate critical point of full Morse index, small closed superlevels are
closed discs, with the deficit from the maximum equal to the squared radial coordinate. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_local_superlevel_homeomorph_closedBall
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hidx : manifoldMorseIndex I f x = Module.finrank ℝ E) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ R > 0, ∀ r, 0 ≤ r → r < R →
      ∃ e : {y : M // y ∈ U ∧ f x - r ^ 2 ≤ f y} ≃ₜ
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ∀ y : {y : M // y ∈ U ∧ f x - r ^ 2 ≤ f y},
          f y = f x - ‖(e y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ 2 := by
  have hneg : manifoldMorseIndex I (-f) x = 0 := by
    have := h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  obtain ⟨U, hU, hxU, R, hR, he⟩ := h.neg.exists_local_sublevel_homeomorph_closedBall
    (hf.mono fun y hy ↦ contDiff_neg.contMDiff.contMDiffAt.comp y hy) hneg
  refine ⟨U, hU, hxU, R, hR, fun r hr hrR ↦ ?_⟩
  obtain ⟨e, he⟩ := he r hr hrR
  have hset : {y | y ∈ U ∧ f x - r ^ 2 ≤ f y} =
      {y | y ∈ U ∧ (-f) y ≤ (-f) x + r ^ 2} := by
    ext y
    simp only [mem_ofPred_eq, Pi.neg_apply]
    constructor <;> rintro ⟨hy, hfy⟩ <;> exact ⟨hy, by linarith⟩
  refine ⟨(Homeomorph.setCongr hset).trans e, fun y ↦ ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  have hy := he ((Homeomorph.setCongr hset) y)
  simp only [Function.comp_apply, Pi.neg_apply, Homeomorph.setCongr_apply] at hy
  linarith

/-- If a function has a unique global minimum at a nondegenerate critical point and one compact
sublevel strictly above it on which it is continuous, all sufficiently small whole sublevels are
closed discs. The radial coordinate records the function value. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_sublevel_homeomorph_closedBall
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    {a : ℝ} (hcompact : IsCompact {y | f y ≤ a}) (hcont : ContinuousOn f {y | f y ≤ a})
    (ha : f x < a)
    (hmin : ∀ y, f y ≤ f x → y = x) :
    ∃ R > 0, ∀ r, 0 ≤ r → r < R →
      ∃ e : {y : M // f y ≤ f x + r ^ 2} ≃ₜ
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ∀ y : {y : M // f y ≤ f x + r ^ 2},
          f y = f x + ‖(e y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ 2 := by
  have hlocal : IsLocalMin f x := Filter.Eventually.of_forall fun y ↦ by
    by_contra! hy
    exact hy.ne (congrArg f (hmin y hy.le))
  have hidx := manifoldMorseIndex_eq_zero_of_isLocalMin
    ((hf.self_of_nhds).of_le (by norm_cast)) hlocal
  obtain ⟨U, hU, hxU, R, hR, he⟩ := h.exists_local_sublevel_homeomorph_closedBall hf hidx
  obtain ⟨ε, hε, hεU⟩ := exists_pos_sublevel_subset_of_unique_min hcompact hcont
    ha hmin hU hxU
  refine ⟨min R (Real.sqrt ε), lt_min hR (Real.sqrt_pos.mpr hε), fun r hr hrR ↦ ?_⟩
  have hrR' : r < R := lt_of_lt_of_le hrR (min_le_left _ _)
  have hrε : r ^ 2 ≤ ε := by
    have := (sq_le_sq₀ hr (Real.sqrt_nonneg ε)).mpr
      (le_of_lt (lt_of_lt_of_le hrR (min_le_right _ _)))
    rwa [Real.sq_sqrt hε.le] at this
  obtain ⟨e, he⟩ := he r hr hrR'
  have hset : {y | f y ≤ f x + r ^ 2} = {y | y ∈ U ∧ f y ≤ f x + r ^ 2} := by
    ext y
    exact ⟨fun hy ↦ ⟨hεU (le_trans hy (add_le_add le_rfl hrε)), hy⟩, And.right⟩
  refine ⟨(Homeomorph.setCongr hset).trans e, fun y ↦ ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  simpa only [Homeomorph.setCongr_apply] using he ((Homeomorph.setCongr hset) y)

end TauCeti
