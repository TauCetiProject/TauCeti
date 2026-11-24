/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.Analysis.Convex.Combination
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.LinearAlgebra.AffineSpace.AffineMap

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

Subdivisions correspond under such a map. A subdivision of `K` is carried to a subdivision of
the image (`Geometry.SimplicialComplex.IsSubdivision.map`), since `f` is still affine on each of
its faces. Conversely every subdivision of the image is the image of a subdivision of `K`
(`Geometry.SimplicialComplex.IsSubdivision.exists_isSubdivision_map_eq`): the inverse of `f` on
`|K|` is again affine on every face of the image, because an affine map injective on the convex
hull of a face has an affine left inverse on its affine span
(`AffineMap.exists_leftInvOn_of_injOn`). So a triangulation of the image polyhedron chosen in the
target, for instance to fit it together with another polyhedron there, is pulled back to a
subdivision of `K` on which `f` is still simplexwise affine.

## Main definitions

* `Geometry.SimplicialComplex.map`: the image of `K` under a map injective on `|K|` and affine on
  every face.

## Main results

* `Geometry.SimplicialComplex.mem_map_faces`: the faces of the image are the images of the faces.
* `Geometry.SimplicialComplex.space_map`: the image complex triangulates `f '' |K|`.
* `Geometry.SimplicialComplex.vertices_map`: its vertices are the images of the vertices of `K`.
* `Geometry.SimplicialComplex.finite_faces_map_iff`: the image has finitely many faces exactly
  when `K` has.
* `Geometry.SimplicialComplex.map_id`, `Geometry.SimplicialComplex.map_map`: functoriality.
* `Geometry.SimplicialComplex.map_invFunOn_map`: the inverse of `f` on `|K|` carries the image of
  `K` back to `K`.
* `Geometry.SimplicialComplex.IsSubdivision.map`: images of subdivisions are subdivisions.
* `Geometry.SimplicialComplex.IsSubdivision.exists_isSubdivision_map_eq`: every subdivision of the
  image of `K` is the image of a subdivision of `K`.

## References

* C. Rourke, B. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and triangulations of polyhedra and of piecewise-linear maps).
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Theorems 10.5–10.6 (linear isomorphisms of subdivisions, fitting together embedded complexes).
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

/-- The image of `K` has finitely many faces exactly when `K` has, since `f` is injective on
`|K|`. -/
theorem finite_faces_map_iff : (K.map f hf haff).faces.Finite ↔ K.faces.Finite := by
  classical
  refine ⟨fun h => ?_, finite_faces_map⟩
  refine (h.subset (image_subset_iff.2 fun s hs =>
    image_mem_map_faces (hf := hf) (haff := haff) hs)).of_finite_image fun s hs s' hs' hss' => ?_
  rw [← coe_inj, ← hf.image_eq_image_iff (K.subset_space hs) (K.subset_space hs'), ← coe_image,
    ← coe_image]
  exact congrArg _ hss'

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

/-- The inverse of `f` on `|K|` is injective on the underlying space of the image of `K`. -/
theorem injOn_invFunOn_space_map :
    InjOn (Function.invFunOn f K.space) (K.map f hf haff).space := by
  rw [space_map]
  exact Function.invFunOn_injOn_image f K.space

/-- The inverse of `f` on `|K|` agrees with an affine map on each face of the image of `K`: an
affine map injective on the convex hull of a face is injective on its affine span, where it has
an affine left inverse. -/
theorem exists_affineMap_eqOn_invFunOn :
    ∀ t ∈ (K.map f hf haff).faces,
      ∃ g : F →ᵃ[𝕜] E, EqOn (Function.invFunOn f K.space) g (convexHull 𝕜 (t : Set F)) := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := mem_map_faces.1 ht
  obtain ⟨g, hg⟩ := haff s hs
  have hinj : InjOn g (affineSpan 𝕜 (s : Set E)) :=
    (g.injOn_affineSpan_iff_injOn_convexHull _).2 ((hf.mono (convexHull_subset_space hs)).congr hg)
  obtain ⟨g', hg'⟩ := g.exists_leftInvOn_of_injOn hinj
  refine ⟨g', ?_⟩
  rw [← hst, ← hg.image_convexHull]
  rintro _ ⟨x, hx, rfl⟩
  rw [hf.leftInvOn_invFunOn (convexHull_subset_space hs hx), hg hx,
    hg' (convexHull_subset_affineSpan _ hx)]

/-- The inverse of `f` on `|K|` carries the image of `K` back to `K`. -/
@[simp]
theorem map_invFunOn_map :
    (K.map f hf haff).map (Function.invFunOn f K.space) injOn_invFunOn_space_map
      exists_affineMap_eqOn_invFunOn = K := by
  classical
  ext t
  simp only [mem_map_faces]
  refine ⟨fun ⟨u, ⟨s, hs, hsu⟩, hut⟩ => ?_, fun ht => ⟨t.image f, ⟨t, ht, coe_image.symm⟩, ?_⟩⟩
  · rw [← hsu, hf.invFunOn_image (K.subset_space hs), coe_inj] at hut
    exact hut ▸ hs
  · rw [coe_image, hf.invFunOn_image (K.subset_space ht)]

/-- **Images of subdivisions are subdivisions.** If `K'` subdivides `K`, then the image of `K'`
under a map injective on `|K|` and affine on every face of `K` subdivides the image of `K`. -/
theorem IsSubdivision.map {K' : SimplicialComplex 𝕜 E} (h : K'.IsSubdivision K)
    {hf' : InjOn f K'.space}
    {haff' : ∀ s ∈ K'.faces, ∃ g : E →ᵃ[𝕜] F, EqOn f g (convexHull 𝕜 (s : Set E))} :
    (K'.map f hf' haff').IsSubdivision (K.map f hf haff) := by
  classical
  refine ⟨by rw [space_map, space_map, h.space_eq], fun t ht => ?_⟩
  obtain ⟨s', hs', hst⟩ := mem_map_faces.1 ht
  obtain ⟨s, hs, hss'⟩ := h.exists_convexHull_subset hs'
  obtain ⟨g, hg⟩ := haff s hs
  refine ⟨s.image f, image_mem_map_faces hs, ?_⟩
  rw [← hst, coe_image, ← (hg.mono hss').image_convexHull, ← hg.image_convexHull]
  exact image_mono hss'

/-- **Subdivisions of an image are images of subdivisions.** Let `f` be injective on `|K|` and
affine on every face of `K`. Every subdivision `L` of the image of `K` under `f` is the image under
`f` of a subdivision `K'` of `K`, namely of the image of `L` under the inverse of `f` on `|K|`. -/
theorem IsSubdivision.exists_isSubdivision_map_eq {L : SimplicialComplex 𝕜 F}
    (hL : L.IsSubdivision (K.map f hf haff)) :
    ∃ (K' : SimplicialComplex 𝕜 E) (hK' : K'.IsSubdivision K),
      K'.map f (hf.mono hK'.space_eq.le) (hK'.exists_affineMap_eqOn haff) = L := by
  classical
  refine ⟨L.map (Function.invFunOn f K.space) (injOn_invFunOn_space_map.mono hL.space_eq.le)
    (hL.exists_affineMap_eqOn exists_affineMap_eqOn_invFunOn), ?_, ?_⟩
  · simpa only [map_invFunOn_map] using hL.map (f := Function.invFunOn f K.space)
      (hf := injOn_invFunOn_space_map) (haff := exists_affineMap_eqOn_invFunOn)
  -- `f` undoes its inverse on `L.space = f '' K.space`.
  have hfi (u : Finset F) (hu : u ∈ L.faces) : f '' (Function.invFunOn f K.space '' u) = u := by
    rw [Set.image_image]
    refine EqOn.image_eq_self fun y hy => Function.invFunOn_eq ?_
    simpa [hL.space_eq] using L.subset_space hu hy
  ext t
  simp only [mem_map_faces]
  refine ⟨fun ⟨s, ⟨u, hu, hus⟩, hst⟩ => ?_, fun ht => ⟨t.image (Function.invFunOn f K.space),
    ⟨t, ht, coe_image.symm⟩, by rw [coe_image, hfi t ht]⟩⟩
  rw [← hus, hfi u hu, coe_inj] at hst
  exact hst ▸ hu

end Geometry.SimplicialComplex
