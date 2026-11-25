/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SimplicialComplex.Map
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision

/-!
# Subdivisions under a simplexwise affine injection

Let `f` be injective on the underlying space `|K|` of a geometric simplicial complex `K` and agree
with an affine map on the convex hull of each face of `K`. Subdivisions correspond under `f`.
A subdivision of `K` is carried to a subdivision of the image `K.map f`
(`Geometry.SimplicialComplex.IsSubdivision.map`), since `f` is still affine on each of its faces
(`Geometry.SimplicialComplex.simplexwise_affine_of_convexHull_subset`). Conversely every
subdivision of the image is the image of exactly one subdivision of `K`
(`Geometry.SimplicialComplex.IsSubdivision.existsUnique_isSubdivision_map_eq`): the inverse of `f`
on `|K|` is again affine on every face of the image
(`Geometry.SimplicialComplex.simplexwise_affine_of_leftInvOn`), and images under `f` of complexes
inside `|K|` determine the complexes (`Geometry.SimplicialComplex.map_inj_of_injOn`). So a
triangulation of the image polyhedron chosen in the target, for instance to fit it together with
another polyhedron there, is pulled back to a subdivision of `K` on which `f` is still simplexwise
affine.

## Main results

* `Geometry.SimplicialComplex.IsSubdivision.map`: images of subdivisions are subdivisions.
* `Geometry.SimplicialComplex.IsSubdivision.existsUnique_isSubdivision_map_eq`: every subdivision
  of the image of `K` is the image of a unique subdivision of `K`.

## References

* C. Rourke, B. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and triangulations of polyhedra and of piecewise-linear maps).
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Theorems 10.5–10.6 (linear isomorphisms of subdivisions, fitting together embedded complexes).
-/

public section

open Finset Set

namespace Geometry.SimplicialComplex

variable {𝕜 E F : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] {K K' : SimplicialComplex 𝕜 E} {f : E → F}
  {hf : InjOn f K.space}
  {haff : ∀ s ∈ K.faces, ∃ g : E →ᵃ[𝕜] F, EqOn f g (convexHull 𝕜 (s : Set E))}

/-- **Images of subdivisions are subdivisions.** If `K'` subdivides `K`, then the image of `K'`
under a map injective on `|K|` and affine on every face of `K` subdivides the image of `K`. -/
theorem IsSubdivision.map (h : K'.IsSubdivision K) :
    (K'.map f (hf.mono h.space_eq.le)
      (simplexwise_affine_of_convexHull_subset h.exists_convexHull_subset haff)).IsSubdivision
        (K.map f hf haff) := by
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
`f` of a unique subdivision `K'` of `K`, namely of the image of `L` under the inverse of `f` on
`|K|`. -/
theorem IsSubdivision.existsUnique_isSubdivision_map_eq {L : SimplicialComplex 𝕜 F}
    (hL : L.IsSubdivision (K.map f hf haff)) :
    ∃! K' : SimplicialComplex 𝕜 E, ∃ hK' : K'.IsSubdivision K,
      K'.map f (hf.mono hK'.space_eq.le)
        (simplexwise_affine_of_convexHull_subset hK'.exists_convexHull_subset haff) = L := by
  have hK' := hL.map (f := Function.invFunOn f K.space) (hf := injOn_invFunOn_space_map)
    (haff := simplexwise_affine_of_leftInvOn hf.leftInvOn_invFunOn)
  rw [map_invFunOn_map] at hK'
  -- `f` undoes its inverse on `L.space = f '' K.space`.
  have hleft : LeftInvOn f (Function.invFunOn f K.space) L.space := by
    rw [hL.space_eq, space_map]
    exact (surjOn_image f K.space).rightInvOn_invFunOn
  refine ⟨_, ⟨hK', map_map_of_leftInvOn hleft⟩, fun K₁ ⟨hK₁, hK₁L⟩ => ?_⟩
  exact (map_inj_of_injOn (hf.mono (union_subset
      (K₁.vertices_subset_space.trans hK₁.space_eq.le)
      (vertices_subset_space.trans hK'.space_eq.le)))
    (hf₂ := hf.mono hK'.space_eq.le)
    (haff₂ := simplexwise_affine_of_convexHull_subset hK'.exists_convexHull_subset haff)).1
    (hK₁L.trans (map_map_of_leftInvOn hleft).symm)

end Geometry.SimplicialComplex
