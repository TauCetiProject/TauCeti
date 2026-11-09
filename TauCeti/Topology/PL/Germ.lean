/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Homogeneous
public import TauCeti.Topology.PL.Map

/-!
# The germ of a piecewise-linear map is conical

Near a point `x`, a piecewise-linear map `f` is the cone on its values near `x`: it is affine
along every segment from `x` to a nearby point. Indeed, only the finitely many cells of a
piecewise-affine decomposition that contain `x` meet a small neighbourhood of `x`, and each of
them is convex, so it contains the whole segment from `x` to any of its points; on that segment
`f` agrees with one affine map (`TauCeti.IsPLWithinAt.eventually_apply_lineMap`).

When `f` is piecewise linear on a neighbourhood of `x`, this local structure is a single global
object. Near `x` a convex polyhedron containing `x` is the translate of a polyhedral cone
(`TauCeti.IsConvexPolyhedron.exists_cone`), and the linear parts of the affine pieces of `f` on
these cones assemble into one map `L : E → F` which is

* piecewise affine on the whole space, with finitely many polyhedral cones as cells;
* positively homogeneous, `L (c • v) = c • L v` for `c ≥ 0`;
* the germ of `f` at `x`, in the sense that `f y = f x + L (y - x)` for `y` near `x`

(`TauCeti.IsPLWithinAt.exists_eventually_eq_add_homogeneous`). If `f` is injective near `x`, then
`L` is injective (`TauCeti.injective_of_eventually_eq_add`).

Rourke and Sanderson *define* a PL map as one that is conical on a star of each point; these
results show that the cell-by-cell notion `TauCeti.IsPLOn` has that property. Near `x`, the image
of `f` is the cone with vertex `f x` on the image of a small sphere about `x` under `L`.

When `E` is a finite-dimensional real normed space, `F` is a real normed space and `L` vanishes
only at the origin (for example when `f` is injective near `x`, so that `L` is injective), the
radial normalization `Continuous.exists_homeomorph_norm_eq` of the source turns `L` into the cone
over a map of unit spheres, the link of `f` at `x`. This is the local model that reduces questions
about PL embeddings near a point, such as their local flatness, to questions about cones. Without
these hypotheses no such normalization exists: a constant PL map has `L = 0`.

## Main results

* `TauCeti.IsPLWithinAt.eventually_apply_lineMap`: a map PL within a set star-shaped about `x` is
  affine along the segments from `x` to the points of the set near `x`.
* `TauCeti.IsPLWithinAt.exists_eventually_eq_add_homogeneous`: the germ at `x` of a map PL on a
  neighbourhood of `x` is that of `y ↦ f x + L (y - x)`, for a positively homogeneous map `L`
  piecewise affine on the whole space.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, 1.1 (stars and links of points of polyhedra) and 1.4 (PL maps as the maps which are
  conical on a star of each point).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {f : E → F} {s : Set E} {x : E}

/-- **A piecewise-linear map is affine along the segments from a point.** If `f` is piecewise
linear within `s` at `x`, and `s` is star-shaped about `x`, then for every `y ∈ s` close enough
to `x`, `f` is affine on the segment from `x` to `y`:
`f (lineMap x y t) = lineMap (f x) (f y) t` for `t ∈ [0, 1]`. -/
theorem IsPLWithinAt.eventually_apply_lineMap (hf : IsPLWithinAt f s x) (hs : StarConvex ℝ x s) :
    ∀ᶠ y in 𝓝[s] x, ∀ t ∈ Icc (0 : ℝ) 1,
      f (AffineMap.lineMap x y t) = AffineMap.lineMap (f x) (f y) t := by
  obtain ⟨V, hxV, hV, hPA⟩ := isPLWithinAt_iff.1 hf
  obtain ⟨n, C, A, hC, hcov, heq⟩ := isPiecewiseAffineOn_iff.1 hPA
  obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  -- The segments from `x` to the points near `x` stay in `U`.
  have hsegU : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x y t ∈ U := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hc : Continuous fun p : E × ℝ => AffineMap.lineMap x p.1 p.2 := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [nhdsWithin_le_nhds hsegU,
    nhdsWithin_le_nhds ((locallyFinite_of_finite C).eventually_subset (fun i => (hC i).isClosed) x),
    self_mem_nhdsWithin] with y hyU hyC hys t ht
  -- The segment from `x` to `y` lies in `V`.
  have hseg {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap x y τ ∈ V :=
    hUV ⟨hyU τ hτ, hs.segment_subset hys (segment_eq_image_lineMap ℝ x y ▸ ⟨τ, hτ, rfl⟩)⟩
  -- A cell through `y` contains `x`, hence the whole segment, on which `f` is affine.
  have hyV : y ∈ V := by simpa using hseg (right_mem_Icc.2 zero_le_one)
  obtain ⟨i, hyi⟩ := mem_iUnion.1 (hcov hyV)
  have hxi : x ∈ C i := hyC hyi
  rw [heq i ⟨hseg ht, (hC i).convex.lineMap_mem hxi hyi ht⟩, ContinuousAffineMap.apply_lineMap,
    heq i ⟨hxV, hxi⟩, heq i ⟨hyV, hyi⟩]

variable [IsTopologicalAddGroup F]

/-- **The germ of a piecewise-linear map is conical.** If `f` is piecewise linear within a
neighbourhood `s` of `x`, then there is a map `L : E → F`, piecewise affine on the whole space
and positively homogeneous, with `f y = f x + L (y - x)` for all `y` near `x`.

The cells of `L` are polyhedral cones, one for each cell of a piecewise-affine decomposition of
`f` near `x` that contains `x`, and on each of them `L` is the linear part of the affine piece of
`f` on that cell. -/
theorem IsPLWithinAt.exists_eventually_eq_add_homogeneous (hf : IsPLWithinAt f s x)
    (hs : s ∈ 𝓝 x) :
    ∃ L : E → F, IsPiecewiseAffineOn L univ ∧ (∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v) ∧
      ∀ᶠ y in 𝓝 x, f y = f x + L (y - x) := by
  obtain ⟨V, hxV, hV, hPA⟩ := isPLWithinAt_iff.1 hf
  obtain ⟨n, C, A, hC, hcov, heq⟩ := isPiecewiseAffineOn_iff.1 hPA
  rw [nhdsWithin_eq_nhds.2 hs] at hV
  have hV' : ∀ᶠ y in 𝓝 x, y ∈ V := hV
  have hcell := (locallyFinite_of_finite C).eventually_subset (fun i => (hC i).isClosed) x
  -- The cells through `x`, and the polyhedral cone of each of them at `x`.
  let ι := {i : Fin n // x ∈ C i}
  choose K hKpoly hKcone hKsub hKnhds using fun i : ι => (hC i).exists_cone i.2
  have hlim (v : E) : Tendsto (fun c : ℝ => x + c • v) (𝓝 0) (𝓝 x) :=
    (by fun_prop : Continuous fun c : ℝ => x + c • v).tendsto' 0 x (by simp)
  -- Along a ray in a cone, close to `x`, the values of `f` are read off the linear part.
  have hray (i : ι) {v : E} (hv : v ∈ K i) :
      ∀ᶠ c in 𝓝[>] (0 : ℝ), f (x + c • v) = f x + c • (A i).contLinear v := by
    filter_upwards [nhdsWithin_le_nhds ((hlim v).eventually (hV'.and (hKnhds i))),
      self_mem_nhdsWithin] with c ⟨hcV, hcK⟩ hc
    have hci : x + c • v ∈ C i := hcK (by simpa using hKcone i c (le_of_lt hc) v hv)
    have hlin := (A i).contLinear_apply_vsub (x + c • v) x
    rw [vsub_eq_sub, vsub_eq_sub, add_sub_cancel_left, map_smul] at hlin
    rw [heq i ⟨hcV, hci⟩, heq i ⟨hxV, i.2⟩, hlin, add_sub_cancel]
  -- Two cones containing `v` give the same value of the linear parts at `v`.
  have hcompat (i j : ι) {v : E} (hi : v ∈ K i) (hj : v ∈ K j) :
      (A i).contLinear v = (A j).contLinear v := by
    obtain ⟨c, hci, hcj, hc⟩ := ((hray i hi).and ((hray j hj).and self_mem_nhdsWithin)).exists
    exact smul_right_injective F (ne_of_gt hc) (add_left_cancel (hci.symm.trans hcj))
  -- The cones cover the whole space.
  have hcover (v : E) : ∃ i : ι, v ∈ K i := by
    obtain ⟨c, ⟨hcV, hcC⟩, hc⟩ := ((((hlim v).eventually (hV'.and hcell)).filter_mono
      (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hcV)
    have hcv : c • v ∈ K ⟨k, hcC hk⟩ := by simpa using hKsub ⟨k, hcC hk⟩ _ hk
    refine ⟨⟨k, hcC hk⟩, ?_⟩
    have hc0 : c ≠ 0 := ne_of_gt hc
    simpa [smul_smul, inv_mul_cancel₀ hc0] using
      hKcone _ c⁻¹ (inv_nonneg.2 (le_of_lt hc)) _ hcv
  choose idx hidx using hcover
  have hL (i : ι) {v : E} (hv : v ∈ K i) : (A (idx v)).contLinear v = (A i).contLinear v :=
    hcompat _ _ (hidx v) hv
  refine ⟨fun v => (A (idx v)).contLinear v,
    isPiecewiseAffineOn_of_finite (A := fun i : ι => (A i).contLinear.toContinuousAffineMap)
      hKpoly (fun v _ => mem_iUnion.2 ⟨idx v, hidx v⟩)
      (fun i v hv => by simpa using hL i hv.2),
    fun c hc v => ?_, ?_⟩
  · beta_reduce
    rw [hL (idx v) (hKcone _ c hc v (hidx v)), map_smul]
  · filter_upwards [hV', hcell] with y hyV hyC
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hyV)
    have hlin := (A k).contLinear_apply_vsub y x
    rw [vsub_eq_sub, vsub_eq_sub] at hlin
    rw [hL ⟨k, hyC hk⟩ (hKsub ⟨k, hyC hk⟩ y hk), hlin, heq k ⟨hyV, hk⟩, heq k ⟨hxV, hyC hk⟩,
      add_sub_cancel]

end TauCeti
