/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.Analysis.Convex.Combination

/-!
# The image of a geometric simplicial complex under a simplexwise affine injection

Let `K` be a geometric simplicial complex in a vector space `E` over a linearly ordered field, and
let `f : E → F` be a map into another vector space which is injective on the underlying space `|K|`
and agrees with an affine map on each face of `K`. Then the images `f '' s` of the faces `s` of `K`
are again the faces of a geometric simplicial complex `K.map f hf haff` in `F`, whose underlying
space is `f '' |K|` (`Geometry.SimplicialComplex.space_map`) and whose vertices are the images of
the vertices of `K` (`Geometry.SimplicialComplex.vertices_map`).

The affine maps may differ from face to face, so `f` need only be piecewise affine: this is the
situation of a piecewise-linear map after its source has been subdivided so that it is affine on
every simplex. The image complex is then a triangulation of the image polyhedron, and `f` carries
each face of `K` onto a face of it, bijectively on vertices. Such triangulated images are how a
polyhedron triangulated in one piecewise-linear chart is transported to another, the step in
triangulating a piecewise-linear manifold chart by chart.

Two facts make the images of faces into a complex. An affine map injective on the convex hull of
an affinely independent family keeps it affinely independent
(`AffineIndependent.map_of_injOn_convexHull`), so the image of a face is again a simplex. And the
image of the convex hull of a face is the convex hull of its image (`Set.EqOn.image_convexHull`),
so since `f` is injective on `|K|` the convex hulls of two image faces meet in the image of the
intersection of the convex hulls of the faces, which is the convex hull of their common face.

## Main definitions

* `Geometry.SimplicialComplex.map`: the image of `K` under a map injective on `|K|` and affine on
  every face.

## Main results

* `Geometry.SimplicialComplex.mem_map_faces`: the faces of the image are the images of the faces.
* `Geometry.SimplicialComplex.space_map`: the image complex triangulates `f '' |K|`.
* `Geometry.SimplicialComplex.vertices_map`: its vertices are the images of the vertices of `K`.
* `Geometry.SimplicialComplex.map_id`, `Geometry.SimplicialComplex.map_map`: functoriality.

## References

* C. Rourke, B. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and triangulations of polyhedra and of piecewise-linear maps).
-/

public section

open Finset Set

namespace Geometry.SimplicialComplex

variable {𝕜 E F G : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  {K : SimplicialComplex 𝕜 E} {f : E → F} {s : Finset E} {t : Finset F}

open scoped Classical in
/-- The image of a geometric simplicial complex `K` under a map `f` which is injective on the
underlying space of `K` and agrees with an affine map on the convex hull of each face of `K`: its
faces are the images of the faces of `K`, as in the image `PreAbstractSimplicialComplex.map` of the
underlying abstract complex. -/
noncomputable def map (K : SimplicialComplex 𝕜 E) (f : E → F) (hf : InjOn f K.space)
    (haff : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] F, EqOn f g (convexHull 𝕜 (s : Set E))) :
    SimplicialComplex 𝕜 F where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map f
  indep := by
    rintro t ⟨s, hs, hst⟩
    replace hst : f '' (s : Set E) = t := by rw [← hst, coe_image]
    obtain ⟨g, hg⟩ := haff s hs
    have hinj : InjOn g (convexHull 𝕜 (range ((↑) : s → E))) := by
      rw [Subtype.range_coe]
      exact (hf.mono (convexHull_subset_space hs)).congr hg
    have hrange : range (g ∘ ((↑) : s → E)) = t := by
      rw [range_comp, Subtype.range_coe, ← hst]
      exact (hg.mono (subset_convexHull 𝕜 _)).image_eq.symm
    exact ((K.indep hs).map_of_injOn_convexHull g hinj).range.mono hrange.ge
  inter_subset_convexHull := by
    rintro t₁ t₂ ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
    replace h₁ : f '' (s₁ : Set E) = t₁ := by rw [← h₁, coe_image]
    replace h₂ : f '' (s₂ : Set E) = t₂ := by rw [← h₂, coe_image]
    obtain ⟨g₁, hg₁⟩ := haff s₁ hs₁
    obtain ⟨g₂, hg₂⟩ := haff s₂ hs₂
    rw [← h₁, ← h₂, ← hg₁.image_convexHull, ← hg₂.image_convexHull,
      ← hf.image_inter (convexHull_subset_space hs₁) (convexHull_subset_space hs₂),
      ← hf.image_inter (K.subset_space hs₁) (K.subset_space hs₂),
      ← (hg₁.mono (convexHull_mono inter_subset_left)).image_convexHull]
    exact image_mono (K.inter_subset_convexHull hs₁ hs₂)

variable {hf : InjOn f K.space}
  {haff : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] F, EqOn f g (convexHull 𝕜 (s : Set E))}

/-- The faces of the image of `K` are the images of the faces of `K`. -/
@[simp]
theorem mem_map_faces : t ∈ (K.map f hf haff).faces ↔ ∃ s ∈ K.faces, f '' (s : Set E) = t :=
  exists_congr fun _ => and_congr_right fun _ => by classical rw [← coe_inj, coe_image]

/-- The image of a face of `K` is a face of the image of `K`. -/
theorem image_mem_map_faces [DecidableEq F] (hs : s ∈ K.faces) :
    s.image f ∈ (K.map f hf haff).faces :=
  mem_map_faces.2 ⟨s, hs, coe_image.symm⟩

/-- The image of `K` triangulates the image of the underlying space of `K`. -/
@[simp]
theorem space_map : (K.map f hf haff).space = f '' K.space := by
  ext y
  simp only [mem_space_iff, mem_map_faces, mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨s, hs, hst⟩, hy⟩
    obtain ⟨g, hg⟩ := haff s hs
    rw [← hst, ← hg.image_convexHull] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨s, hs, hx⟩, rfl⟩
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    classical
    obtain ⟨g, hg⟩ := haff s hs
    refine ⟨s.image f, ⟨s, hs, coe_image.symm⟩, ?_⟩
    rw [coe_image, ← hg.image_convexHull]
    exact mem_image_of_mem f hx

/-- The vertices of the image of `K` are the images of the vertices of `K`. -/
@[simp]
theorem vertices_map : (K.map f hf haff).vertices = f '' K.vertices := by
  ext y
  simp only [mem_vertices, mem_map_faces, mem_image]
  refine ⟨fun ⟨s, hs, hsy⟩ => ?_, fun ⟨x, hx, hxy⟩ => ⟨{x}, hx, by simp [hxy]⟩⟩
  have hmem {x : E} (hx : x ∈ s) : f x = y := by
    have : f x ∈ f '' (s : Set E) := mem_image_of_mem f hx
    rwa [hsy, coe_singleton, mem_singleton_iff] at this
  obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
  have hsx : s = {x} := eq_singleton_iff_unique_mem.2 ⟨hx, fun x' hx' =>
    hf (K.subset_space hs hx') (K.subset_space hs hx) ((hmem hx').trans (hmem hx).symm)⟩
  exact ⟨x, hsx ▸ hs, hmem hx⟩

/-- The image of a complex with finitely many faces has finitely many faces. -/
theorem finite_faces_map (h : K.faces.Finite) : (K.map f hf haff).faces.Finite :=
  h.image _

/-- Two maps which agree on the underlying space of `K` have the same image complex. -/
theorem map_congr {f' : E → F} (h : EqOn f f' K.space) {hf' : InjOn f' K.space}
    {haff' : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] F, EqOn f' g (convexHull 𝕜 (s : Set E))} :
    K.map f hf haff = K.map f' hf' haff' := by
  ext t
  simp only [mem_map_faces]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  rw [(h.mono (K.subset_space hs)).image_eq]

/-- The image of `K` under the identity is `K`. -/
@[simp]
theorem map_id {hf : InjOn id K.space}
    {haff : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] E, EqOn id g (convexHull 𝕜 (s : Set E))} :
    K.map id hf haff = K := by
  ext t
  simp only [mem_map_faces, image_id, coe_inj, exists_eq_right]

/-- Taking images is functorial: the image under `f₂` of the image of `K` under `f` is the image of
`K` under `f₂ ∘ f`. -/
theorem map_map {f₂ : F → G} {hf₂ : InjOn f₂ (K.map f hf haff).space}
    {haff₂ : ∀ t ∈ (K.map f hf haff).faces, ∃ g : F →ᵃ[𝕜] G, EqOn f₂ g (convexHull 𝕜 (t : Set F))}
    {hf₂₁ : InjOn (f₂ ∘ f) K.space}
    {haff₂₁ : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] G, EqOn (f₂ ∘ f) g (convexHull 𝕜 (s : Set E))} :
    (K.map f hf haff).map f₂ hf₂ haff₂ = K.map (f₂ ∘ f) hf₂₁ haff₂₁ := by
  ext u
  simp only [mem_map_faces]
  refine ⟨fun ⟨t, ⟨s, hs, hst⟩, htu⟩ => ⟨s, hs, by rw [image_comp, hst, htu]⟩,
    fun ⟨s, hs, hsu⟩ => ?_⟩
  classical
  exact ⟨s.image f, ⟨s, hs, coe_image.symm⟩, by rw [coe_image, ← image_comp, hsu]⟩

end Geometry.SimplicialComplex
