/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Segment
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-linear graphs and curves are locally flat

The graph of a continuous map is locally flat, by the continuous-graph theorem in
`TauCeti.Geometry.Manifold.LocallyFlat.Basic`. This file combines that result with the
piecewise-linear continuity theorem for consumers building PL embeddings. The non-affine statement
applies, for example, to the absolute-value PL map. The graph-chart criterion below transports
this local model through an ambient homeomorphism.

It then proves that a piecewise-linear curve is locally flat in every codimension: a topological
embedding `f : N → M` of a manifold modelled on `ℝ` into one modelled on a real Hausdorff locally
convex space `V ≃L[ℝ] ℝ × F'`, piecewise linear when read in charts, is locally flat with
complementary model `F'`. Near a parameter `t` the chart reading `g` of `f` is affine on each side
of `t` (`TauCeti.IsPLOn.exists_eqOn_Icc`), and injective, so near `g t` the image is two segments
from `g t` meeting only there (`TauCeti.IsPLOn.exists_image_Icc_eq_affineSegment`), which are flat
at `g t` (`TauCeti.exists_isSliceChart_of_inter_eq_union_affineSegment`). Since `f` is an
embedding, no other part of the curve comes near the point. For knots, with `N` the circle
`AddCircle p` and `M` a piecewise-linear `3`-manifold such as `ℝ³`, this says that
piecewise-linear knots are locally flat, generalizing the polygonal case
`TauCeti.SimplePolygon.isLocallyFlat_realize`.

The restriction to curves is essential. A piecewise-linear embedding of a manifold of dimension at
least two need not be locally flat in codimension two: the cone on a knotted circle in `S³` is a
piecewise-linear disc in the four-ball which is not locally flat at the cone point. For a curve the
link of a point is a pair of points in a sphere, which is never knotted.

## Main results

* `TauCeti.IsPLOn.isLocallyFlat_graph`: the graph of a globally PL map is locally flat.
* `TauCeti.IsLocallyFlat.of_isPLOn_chartAt`: an embedding of a manifold modelled on `ℝ` which is
  piecewise linear in charts is locally flat.
* `TauCeti.IsLocallyFlat.of_isPLOn_comp_chartAt_symm`: the same for a curve in the model space
  itself, such as a piecewise-linear knot in `ℝ³`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for piecewise-linear maps, and stars and links of points of polyhedra.
-/

public section

namespace TauCeti

/-- A map piecewise linear on all of `E` has a locally flat graph `x ↦ (x, f x)` with
complementary model `F`. -/
theorem IsPLOn.isLocallyFlat_graph
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] {f : E → F}
    (hf : IsPLOn f (Set.univ : Set E)) :
    IsLocallyFlat E F (fun x : E => (x, f x)) :=
  TauCeti.isLocallyFlat_graph f (continuousOn_univ.mp hf.continuousOn)

/-- A globally PL map is locally flat when an ambient homeomorphism presents its image as a graph.
The section equation `(Φ (f x)).1 = x` identifies `f` with that graph, with complementary model
`F`. -/
theorem IsPLOn.isLocallyFlat_of_homeomorph_graph
    {E M F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [AddGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    {f : E → M} (hf : IsPLOn f (Set.univ : Set E)) (Φ : M ≃ₜ E × F)
    (hΦ : ∀ x, (Φ (f x)).1 = x) :
    IsLocallyFlat E F f :=
  (continuousOn_univ.mp hf.continuousOn).isLocallyFlat_of_homeomorph_graph Φ hΦ

/-- A piecewise-linear map on an open domain has a locally flat graph in the ambient product.
This is the PL corollary of `ContinuousOn.isLocallyFlat_graph_of_isOpen`, and is the graph form
used when a PL embedding is described in coordinate charts. -/
theorem IsPLOn.isLocallyFlat_graph_of_isOpen
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : IsPLOn f s) :
    IsLocallyFlat s F (fun x : s => ((x.1, f x.1) : E × F)) :=
  _root_.ContinuousOn.isLocallyFlat_graph_of_isOpen hf.continuousOn hs

section Curve

open Set Topology

variable {N M V F' : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [TopologicalSpace M] [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V]
  [ChartedSpace V M]

/-- **Piecewise-linear curves are locally flat.** Let `N` be a manifold modelled on `ℝ`, and `M`
one modelled on a real Hausdorff locally convex space `V ≃L[ℝ] ℝ × F'`. A topological embedding
`f : N → M` which, read in the charts at each point and at its image, is piecewise linear near
that point, is locally flat with complementary model `F'`. -/
theorem IsLocallyFlat.of_isPLOn_chartAt (e : V ≃L[ℝ] ℝ × F') {f : N → M} (hf : IsEmbedding f)
    (hPL : ∀ x, ∃ s ∈ 𝓝 (chartAt ℝ x x), IsPLOn (chartAt V (f x) ∘ f ∘ (chartAt ℝ x).symm) s) :
    IsLocallyFlat ℝ F' f := by
  refine isLocallyFlat_iff_isSliceEmbedding.2 ⟨hf, fun x => ?_⟩
  obtain ⟨s, hs, hgPL⟩ := hPL x
  set c := chartAt ℝ x
  set d := chartAt V (f x)
  set g := d ∘ f ∘ c.symm
  set t := c x
  -- The chart reading `g` of `f` is defined, and injective, on the open set `D` around `t`.
  set D := c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)
  have hxt : c.symm t = x := c.left_inv (mem_chart_source ℝ x)
  have hD : D ∈ 𝓝 t := (c.isOpen_inter_preimage_symm
    (d.open_source.preimage hf.continuous)).mem_nhds ⟨mem_chart_target ℝ x, by
      simp [hxt, d, mem_chart_source]⟩
  have hinj : InjOn g D := fun u hu v hv huv =>
    c.symm.injOn (by simpa using hu.1) (by simpa using hv.1)
      (hf.injective (d.injOn hu.2 hv.2 huv))
  obtain ⟨ε, hε, hεD, himA, himB, ha, hb, hab⟩ :=
    hgPL.exists_image_Icc_eq_affineSegment hs hD hinj
  -- As `f` is an embedding, the image of `g` near `g t` comes from parameters near `t` alone.
  obtain ⟨O, hO, hOW⟩ := hf.isInducing.isOpen_iff.1 <| c.isOpen_image_symm_of_subset_target
    isOpen_Ioo fun u hu => (hεD ⟨hu.1.le, hu.2.le⟩).1
  set U := d.target ∩ d.symm ⁻¹' O
  have hgt : g t = d (f x) := by simp [g, hxt]
  have hzU : g t ∈ U := by
    rw [hgt]
    refine ⟨d.map_source (mem_chart_source V (f x)), ?_⟩
    rw [mem_preimage, d.left_inv (mem_chart_source V (f x)), ← mem_preimage, hOW]
    exact ⟨t, ⟨by linarith, by linarith⟩, hxt⟩
  have hUA : U ∩ d.symm ⁻¹' range f =
      U ∩ (affineSegment ℝ (g t) (g (t - ε)) ∪ affineSegment ℝ (g t) (g (t + ε))) := by
    ext y
    rw [← himA, ← himB]
    refine and_congr_right fun hy => ⟨?_, ?_⟩
    · rintro ⟨m, hm⟩
      obtain ⟨u, hu, rfl⟩ : m ∈ c.symm '' Ioo (t - ε) (t + ε) := by
        rw [← hOW, mem_preimage, hm]
        exact hy.2
      have hyu : y = g u := by simp [g, hm, d.right_inv hy.1]
      rcases le_total u t with hut | htu
      · exact .inl ⟨u, ⟨hu.1.le, hut⟩, hyu.symm⟩
      · exact .inr ⟨u, ⟨htu, hu.2.le⟩, hyu.symm⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;>
      · exact ⟨c.symm u, (d.left_inv (hεD ⟨by linarith [hu.1], by linarith [hu.2]⟩).2).symm⟩
  -- The two segments are flat at `g t`; reading that chart through `d` flattens `range f`.
  obtain ⟨ψ, hzψ, hψ⟩ := exists_isSliceChart_of_inter_eq_union_affineSegment e ha hb hab
    ((d.isOpen_inter_preimage_symm hO).mem_nhds hzU) hUA
  refine ⟨d.trans ψ, ⟨mem_chart_source V (f x), (hgt ▸ hzψ : d (f x) ∈ ψ.source)⟩,
    isSliceChart_iff.2 fun y hy => ?_⟩
  rw [← (hψ.comp d).mem_iff hy, mem_inter_iff, mem_preimage, mem_preimage, d.left_inv hy.1]
  exact (and_iff_right hy.1).symm

/-- **Piecewise-linear curves in a model space are locally flat.** In a real Hausdorff locally
convex space `V ≃L[ℝ] ℝ × F'`, a topological embedding `f : N → V` of a manifold modelled on `ℝ`
which is piecewise linear in the charts of `N` is locally flat with complementary model `F'`. For
`N = AddCircle p` and `V = ℝ³` these are the piecewise-linear knots. -/
theorem IsLocallyFlat.of_isPLOn_comp_chartAt_symm (e : V ≃L[ℝ] ℝ × F') {f : N → V}
    (hf : IsEmbedding f) (hPL : ∀ x, ∃ s ∈ 𝓝 (chartAt ℝ x x), IsPLOn (f ∘ (chartAt ℝ x).symm) s) :
    IsLocallyFlat ℝ F' f :=
  .of_isPLOn_chartAt e hf (by simpa using hPL)

end Curve

end TauCeti
