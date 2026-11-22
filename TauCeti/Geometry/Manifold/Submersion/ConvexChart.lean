/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Convexity charts at regular points

Let `f : M → F` be a smooth map from a finite-dimensional boundaryless real manifold to a
finite-dimensional real normed space, and let `x` be a regular point of `f`: the differential of
`f` at `x` is surjective. By the submersion normal form
(`ContMDiffOn.exists_domChart_mem_maximalAtlas_of_surjective_mfderiv`), `f` reads near `x` as a
surjective linear map `F × K → F` in a suitable chart. The preimage of a small ball under that
chart is then a convexity chart of `f` in the sense of the local-to-global principle
(`TauCeti.IsConvexChart`): `f` maps it onto the open convex image of the ball under that linear
map, it is open onto that image, and its fibres are images of convex slices of the ball, hence
preconnected (`ContMDiffOn.exists_isConvexChart_subset_of_surjective_mfderiv`).

So near regular points every smooth map into a finite-dimensional space is locally convex. In the
convexity theorems for moment maps this supplies the convexity charts at the points where the
action is locally free, leaving only the points with nontrivial isotropy to the local normal form
of the action.

## Main results

* `ContMDiffOn.exists_isConvexChart_subset_of_surjective_mfderiv`: every neighbourhood of a
  regular point of a smooth map into a finite-dimensional real normed space contains a convexity
  chart of the map around that point.

## References

* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Section 3 (local convexity of maps).
-/

public section

open Function Set Filter Metric
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M] {f : M → F} {x : M}

/-- **Convexity charts at a regular point.** Let `f : M → F` be a map from a finite-dimensional
boundaryless real manifold to a finite-dimensional real normed space, `C^n` with `1 ≤ n` on an open
neighbourhood of `x`, with surjective differential at `x`. Then every neighbourhood of `x` contains
a convexity chart of `f` containing `x`. -/
theorem _root_.ContMDiffOn.exists_isConvexChart_subset_of_surjective_mfderiv {U : Set M}
    (hfU : ContMDiffOn I 𝓘(ℝ, F) n f U) (hU : IsOpen U) (hxU : x ∈ U) (hn : 1 ≤ n)
    (hs : Surjective (mfderiv I 𝓘(ℝ, F) f x)) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ V ⊆ N, x ∈ V ∧ IsConvexChart f V := by
  obtain ⟨φ, L, hxφ, -, -, hEq⟩ :=
    hfU.exists_domChart_mem_maximalAtlas_of_surjective_mfderiv hU hxU hn hs
  -- In the chart `e = I ∘ φ`, `f` is the surjective linear map `g = pr₁ ∘ L`.
  let e := φ.transHomeomorph I.toHomeomorph
  let g := LinearMap.fst ℝ F _ ∘ₗ L.toLinearEquiv.toLinearMap
  have hg : IsOpenMap g := LinearMap.isOpenMap_of_finiteDimensional g fun v ↦
    ⟨L.symm (v, 0), by simp [g]⟩
  have hfe : EqOn f (g ∘ e) e.source := fun z hz ↦ by
    have hz' : z ∈ (φ.extend I).source := by rwa [φ.extend_source]
    -- At `φ.extend I z = I (φ z)`, `hEq` reads `f (φ.symm (φ z)) = (L (I (φ z))).1` (the target
    -- chart of the model space `F` is the identity), which is `f z = g (e z)` by `φ.left_inv`.
    simpa [extChartAt_model_space_eq_id, φ.left_inv hz, e, g] using
      hEq ((φ.extend I).map_source hz')
  -- Shrink to the preimage of a ball inside the image of `N`.
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1
    (e.image_mem_nhds hxφ (inter_mem hN (e.open_source.mem_nhds hxφ)))
  have hBt : ball (e x) r ⊆ e.target := hrN.trans <| (image_mono inter_subset_right).trans
    e.image_source_eq_target.subset
  refine ⟨e.source ∩ e ⁻¹' ball (e x) r, fun z ⟨hz, hzr⟩ ↦ ?_, ⟨hxφ, mem_ball_self hr⟩,
    isConvexChart_source_inter_preimage hg hfe isOpen_ball (convex_ball _ _) hBt⟩
  obtain ⟨y, ⟨hyN, hy⟩, hyz⟩ := hrN hzr
  rwa [← e.injOn hy hz hyz]

end TauCeti
