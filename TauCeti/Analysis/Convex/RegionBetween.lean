/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import TauCeti.Analysis.Convex.Intrinsic
public import TauCeti.Topology.Order.RegionBetween

/-!
# Graphs and bands of affine functions

Over a simplex `convexHull ℝ s` of a real vector space, the graph of an affine function and the
closed band `TauCeti.closedRegionBetween a b (convexHull ℝ s)` between two ordered affine
functions `a ≤ b` are convex polytopes. These are the *rectilinear cells* of Łojasiewicz's
triangulation of semianalytic sets: the cells whose simplicial subdivision
(`Geometry.SimplicialComplex.exists_subdivision`) produces the triangulating complex. This file
describes them in the terms that subdivision needs.

* `AffineMap.graphOn_convexHull`: the graph of an affine map over the convex hull of `s` is the
  convex hull of its graph over `s`. Over a simplex, the graph cell is the simplex spanned by the
  graph points over its vertices.
* `TauCeti.closedRegionBetween_convexHull`: if `a ≤ b` on `s`, the closed band between `a` and `b`
  over the convex hull of `s` is the convex hull of the lower vertices `(x, a x)` and the upper
  vertices `(x, b x)`, `x ∈ s`. Over a finite set `s` it is therefore a polytope; where `a = b` it
  collapses to the graph (`TauCeti.closedRegionBetween_self`).
* `ContinuousAffineMap.intrinsicInterior_graphOn`, `ContinuousAffineMap.intrinsicFrontier_graphOn`:
  the intrinsic interior and frontier of the graph of a continuous affine map lie over the
  intrinsic interior and frontier of its domain.
* `TauCeti.intrinsicInterior_closedRegionBetween`: if `a ≤ b` on `s`, with `a < b` somewhere on
  `s`, the intrinsic interior of the closed band is the open band over the intrinsic interior of
  `s`. For closed `s`, its intrinsic frontier therefore consists of the lower graph, the upper graph
  and the closed band over the intrinsic frontier of `s`
  (`TauCeti.intrinsicFrontier_closedRegionBetween`).

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §2, Lemma 15, and §4.
-/

public section

open Filter Set Topology

section ConvexHull

variable {𝕜 E F : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The graph of an affine map over the convex hull of `s` is the convex hull of its graph over
`s`. -/
theorem AffineMap.graphOn_convexHull (f : E →ᵃ[𝕜] F) (s : Set E) :
    (convexHull 𝕜 s).graphOn f = convexHull 𝕜 (s.graphOn f) := by
  have h : ∀ t : Set E, t.graphOn f = (AffineMap.id 𝕜 E).prod f '' t := fun t ↦ by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [h, h, AffineMap.image_convexHull]

end ConvexHull

namespace TauCeti

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The closed band between a convex function and a concave function over a convex set is
convex. -/
theorem _root_.ConvexOn.convex_closedRegionBetween {f g : E → ℝ} {s : Set E}
    (hf : ConvexOn ℝ s f) (hg : ConcaveOn ℝ s g) : Convex ℝ (closedRegionBetween f g s) := by
  convert hf.convex_epigraph.inter hg.convex_hypograph using 1
  ext p
  simp only [mem_closedRegionBetween, mem_Icc, mem_inter_iff, mem_ofPred_eq]
  tauto

/-- **Vertex description of a rectilinear band.** If `a ≤ b` on `s`, the closed band between the
affine functions `a` and `b` over the convex hull of `s` is the convex hull of the lower vertices
`(x, a x)` and the upper vertices `(x, b x)` for `x ∈ s`. -/
theorem closedRegionBetween_convexHull {a b : E →ᵃ[ℝ] ℝ} {s : Set E}
    (hab : ∀ x ∈ s, a x ≤ b x) :
    closedRegionBetween a b (convexHull ℝ s) = convexHull ℝ (s.graphOn a ∪ s.graphOn b) := by
  refine Subset.antisymm ?_ (convexHull_min ?_ ?_)
  · -- `(x, t)` lies on the vertical segment from `(x, a x)` to `(x, b x)`
    rintro ⟨x, t⟩ hp
    obtain ⟨hx, hax, hxb⟩ := mem_closedRegionBetween.1 hp
    have hgraph : ∀ f : E →ᵃ[ℝ] ℝ, s.graphOn f ⊆ s.graphOn a ∪ s.graphOn b →
        (x, f x) ∈ convexHull ℝ (s.graphOn a ∪ s.graphOn b) := fun f hf ↦
      convexHull_mono hf (f.graphOn_convexHull s ▸ ⟨x, hx, rfl⟩)
    refine (convex_convexHull ℝ _).segment_subset (hgraph a subset_union_left)
      (hgraph b subset_union_right) ?_
    rw [← Prod.image_mk_segment_right, segment_eq_Icc (hax.trans hxb)]
    exact ⟨t, ⟨hax, hxb⟩, rfl⟩
  · rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact mem_closedRegionBetween.2 ⟨subset_convexHull ℝ s hx, le_rfl, hab x hx⟩
    · exact mem_closedRegionBetween.2 ⟨subset_convexHull ℝ s hx, hab x hx, le_rfl⟩
  · have hs := convex_convexHull ℝ s
    refine ConvexOn.convex_closedRegionBetween ?_ ?_
    · rw [a.decomp]
      exact (a.linear.convexOn hs).add (convexOn_const _ hs)
    · rw [b.decomp]
      exact (b.linear.concaveOn hs).add (concaveOn_const _ hs)

end Convex

end TauCeti

/-! ### Intrinsic interiors and frontiers of graphs -/

section Graph

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]

namespace ContinuousAffineMap

variable [IsTopologicalAddGroup E] (f : E →ᴬ[𝕜] F)

/-- The shear `(x, y) ↦ (x, y + f x)`, which carries `s ×ˢ {0}` onto the graph of `f` over `s`. -/
private def graphShear : E × F ≃ᴬ[𝕜] E × F :=
  ((ContinuousLinearEquiv.refl 𝕜 E).skewProd (ContinuousLinearEquiv.refl 𝕜 F)
    f.contLinear).toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd 𝕜 (E × F) ((0 : E), f 0))

private theorem graphShear_apply (p : E × F) : graphShear f p = (p.1, p.2 + f p.1) := by
  rw [graphShear, ContinuousAffineEquiv.trans_apply, ← ContinuousAffineEquiv.coe_coe,
    ContinuousAffineEquiv.constVAdd_coe, AffineEquiv.constVAdd_apply,
    ContinuousLinearEquiv.coe_toContinuousAffineEquiv, ContinuousLinearEquiv.skewProd_apply]
  have hf : f p.1 = (f : E →ᵃ[𝕜] F).linear p.1 + f 0 := congrFun (f : E →ᵃ[𝕜] F).decomp p.1
  simp only [vadd_eq_add, Prod.mk_add_mk, zero_add, hf, ContinuousLinearEquiv.refl_apply,
    ContinuousAffineMap.coe_contLinear, Prod.mk.injEq, true_and]
  abel

private theorem graphOn_eq_image_graphShear (s : Set E) :
    s.graphOn f = graphShear f '' (s ×ˢ {0}) := by
  ext ⟨x, y⟩
  simp [graphShear_apply, eq_comm]

/-- The intrinsic interior of the graph of a continuous affine map over `s` is its graph over the
intrinsic interior of `s`. -/
theorem intrinsicInterior_graphOn (s : Set E) :
    intrinsicInterior 𝕜 (s.graphOn f) = (intrinsicInterior 𝕜 s).graphOn f := by
  rw [graphOn_eq_image_graphShear, ContinuousAffineEquiv.intrinsicInterior_image,
    intrinsicInterior_prod_eq, intrinsicInterior_singleton, graphOn_eq_image_graphShear]

/-- The intrinsic frontier of the graph of a continuous affine map over a closed set `s` is its
graph over the intrinsic frontier of `s`. -/
theorem intrinsicFrontier_graphOn [T1Space F] {s : Set E} (hs : IsClosed s) :
    intrinsicFrontier 𝕜 (s.graphOn f) = (intrinsicFrontier 𝕜 s).graphOn f := by
  have hg : IsClosed (s.graphOn f) := by
    rw [graphOn_eq_image_graphShear]
    exact (graphShear f).toHomeomorph.isClosedMap _ (hs.prod isClosed_singleton)
  rw [← hg.sdiff_intrinsicInterior, intrinsicInterior_graphOn, ← hs.sdiff_intrinsicInterior]
  exact (image_sdiff (fun _ _ h ↦ congrArg Prod.fst h) _ _).symm

end ContinuousAffineMap

end Graph

/-! ### Intrinsic interiors and frontiers of bands -/

namespace TauCeti

section Band

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E →ᴬ[ℝ] ℝ} {s : Set E}

/-- A band which is nondegenerate somewhere has the same affine span as the vertical cylinder over
its base. -/
private theorem affineSpan_closedRegionBetween (hab : ∀ x ∈ s, a x ≤ b x)
    (h : ∃ x ∈ s, a x < b x) :
    affineSpan ℝ (closedRegionBetween a b s) = affineSpan ℝ (s ×ˢ (univ : Set ℝ)) := by
  refine le_antisymm (affineSpan_mono ℝ fun p hp ↦ mk_mem_prod (mem_closedRegionBetween.1 hp).1
    (mem_univ _)) (affineSpan_le.2 ?_)
  obtain ⟨x₀, hx₀, hlt⟩ := h
  have hmem : ∀ x ∈ s, ∀ t ∈ Icc (a x) (b x),
      (x, t) ∈ affineSpan ℝ (closedRegionBetween a b s) :=
    fun x hx t ht ↦ subset_affineSpan ℝ _ (mem_closedRegionBetween.2 ⟨hx, ht⟩)
  -- the nondegenerate fibre over `x₀` puts the vertical direction in the span
  have hv : ((0 : E), (1 : ℝ)) ∈ (affineSpan ℝ (closedRegionBetween a b s)).direction := by
    have := Submodule.smul_mem _ (b x₀ - a x₀)⁻¹ <| AffineSubspace.vsub_mem_direction
      (hmem x₀ hx₀ (b x₀) ⟨hlt.le, le_rfl⟩) (hmem x₀ hx₀ (a x₀) ⟨le_rfl, hlt.le⟩)
    convert this using 1
    simp [inv_mul_cancel₀ (sub_pos.2 hlt).ne']
  rintro ⟨x, t⟩ ⟨hx, -⟩
  convert AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ (t - a x) hv)
    (hmem x hx (a x) ⟨le_rfl, hab x hx⟩) using 1
  simp

/-- **Intrinsic interior of a band.** If `a ≤ b` on `s`, with `a < b` somewhere on `s`, the
intrinsic interior of the closed band between the continuous affine functions `a` and `b` over `s`
is the open band over the intrinsic interior of `s`. -/
theorem intrinsicInterior_closedRegionBetween (hab : ∀ x ∈ s, a x ≤ b x)
    (h : ∃ x ∈ s, a x < b x) :
    intrinsicInterior ℝ (closedRegionBetween a b s) =
      regionBetween a b (intrinsicInterior ℝ s) := by
  have hspan := affineSpan_closedRegionBetween hab h
  have hcyl : intrinsicInterior ℝ (s ×ˢ (univ : Set ℝ)) = intrinsicInterior ℝ s ×ˢ univ := by
    rw [intrinsicInterior_prod_eq]
    simp [intrinsicInterior]
  refine Subset.antisymm ?_ ?_
  · rintro ⟨x, t⟩ hp
    have hx : x ∈ intrinsicInterior ℝ s := by
      have := intrinsicInterior_mono_of_affineSpan_eq
        (fun p hp ↦ mk_mem_prod (mem_closedRegionBetween.1 hp).1 (mem_univ _)) hspan hp
      rw [hcyl] at this
      exact this.1
    -- moving vertically in either direction stays in the band, so `t` is strictly inside
    have hxs : x ∈ s := (mem_closedRegionBetween.1 (intrinsicInterior_subset hp)).1
    have hv : ((0 : E), (1 : ℝ)) ∈ (affineSpan ℝ (closedRegionBetween a b s)).direction := by
      rw [hspan, direction_affineSpan]
      simpa using vsub_mem_vectorSpan ℝ (mk_mem_prod hxs (mem_univ (t + 1)))
        (mk_mem_prod hxs (mem_univ t))
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), a x ≤ t + ε ∧ t + ε ≤ b x := by
      filter_upwards [eventually_add_smul_mem_of_mem_intrinsicInterior hp hv] with ε hε
      simpa using (mem_closedRegionBetween.1 hε).2
    obtain ⟨ε, ⟨-, hε⟩, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))
    obtain ⟨δ, ⟨hδ, -⟩, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin).exists (f := 𝓝[<] (0 : ℝ))
    exact ⟨hx, by linarith [mem_Iio.1 hδ0], by linarith [mem_Ioi.1 hε0]⟩
  · rintro ⟨x, t⟩ ⟨hx, hax, hxb⟩
    have hU : IsOpen {p : E × ℝ | a p.1 < p.2 ∧ p.2 < b p.1} :=
      (isOpen_lt (a.continuous.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd (b.continuous.comp continuous_fst))
    refine intrinsicInterior_inter_subset_of_affineSpan_eq hU ?_ hspan
      ⟨by rw [hcyl]; exact ⟨hx, mem_univ t⟩, hax, hxb⟩
    rintro p ⟨⟨hp, -⟩, h₁, h₂⟩
    exact mem_closedRegionBetween.2 ⟨hp, h₁.le, h₂.le⟩

/-- **Intrinsic frontier of a band.** If `a ≤ b` on a closed set `s`, with `a < b` somewhere on
`s`, the intrinsic frontier of the closed band between the continuous affine functions `a` and `b`
over `s` consists of the graphs of `a` and `b` over `s` and the closed band over the intrinsic
frontier of `s`. -/
theorem intrinsicFrontier_closedRegionBetween (hs : IsClosed s) (hab : ∀ x ∈ s, a x ≤ b x)
    (h : ∃ x ∈ s, a x < b x) :
    intrinsicFrontier ℝ (closedRegionBetween a b s) =
      s.graphOn a ∪ s.graphOn b ∪ closedRegionBetween a b (intrinsicFrontier ℝ s) := by
  rw [← (isClosed_closedRegionBetween hs a.continuous.continuousOn
      b.continuous.continuousOn).sdiff_intrinsicInterior,
    intrinsicInterior_closedRegionBetween hab h, ← hs.sdiff_intrinsicInterior]
  ext ⟨x, t⟩
  have := hab x
  simp only [Set.mem_sdiff, mem_closedRegionBetween, regionBetween, mem_ofPred_eq, mem_Icc,
    mem_Ioo, mem_union, mem_graphOn]
  grind

end Band

end TauCeti
