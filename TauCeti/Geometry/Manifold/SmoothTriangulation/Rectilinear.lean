/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Geometric
public import TauCeti.Geometry.Manifold.SmoothTriangulation.StarImmersion

/-!
# Smooth triangulations from rectilinear complexes

A geometric simplicial complex `K` in a real normed space `V` is read as an abstract complex
through its vertex scheme, and the comparison map `K.realizationToAmbient : |K.vertexScheme| → V`
(`TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Geometric`) sends a point with
barycentric coordinates `x` to `∑ v, x v • v`. This map is linear in barycentric coordinates on
every closed simplex and injective, so it is its own secant map
(`Geometry.SimplicialComplex.secantMap_realizationToAmbient`) and an injective star immersion
of every class `Cⁿ`. For finite vertex schemes and regularity at least `C¹`, the separation,
perturbation and secant approximation theorems apply with their individual further hypotheses,
including an ordered vertex type for edgewise subdivision and a smooth cutoff for interpolation.

Following the comparison map by a map `F : V → M` into a manifold gives an immersion of a
closed simplex as soon as `F` is `Cⁿ` on that simplex with a derivative injective on the
directions of its affine span. If a homeomorphism from `K.space` onto `M` agrees on each closed
simplex with such a map `F`, allowed to depend on the face, and the closed simplices form a locally
finite family in `K.space`, composing with `K.realizationHomeomorph` gives a `Cⁿ` triangulation
(`TauCeti.IsSmoothTriangulation`). The derivative is asked to be injective only along the
simplices, not on all of `V`: the radial projection of the boundary of a tetrahedron onto the
sphere around an interior point kills the radial direction, which is transverse to every face.

This is how a rectilinear complex in a coordinate chart, such as the complexes produced there by
subdivision and by triangulating unions of polyhedra, becomes an embedded smooth complex in a
manifold, the local form in which Whitehead's and Munkres' construction of a smooth triangulation
fits triangulations together.

## Main results

* `Geometry.SimplicialComplex.isStarImmersion_realizationToAmbient`: the comparison map is a star
  immersion of every class.
* `Geometry.SimplicialComplex.isSimplexImmersion_comp_realizationToAmbient_comp_faceInclusion`:
  following it by a map `F` which is `Cⁿ` within a closed simplex, and has at every point of it a
  derivative within the simplex injective on the directions of its affine span, gives a `Cⁿ`
  immersion of that simplex.
* `Geometry.SimplicialComplex.isSmoothTriangulation_realizationHomeomorph_trans`: a homeomorphism
  from a rectilinear polyhedron, locally finite in itself, onto a manifold, which is the
  restriction on each closed simplex of a map `Cⁿ` within that simplex with derivatives injective
  along it, is a smooth triangulation.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Definitions 8.1–8.3 and Theorems 10.5–10.6.
-/

public section

noncomputable section

open Set Function AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff

namespace Geometry.SimplicialComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : SimplicialComplex ℝ V}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

/-- The comparison map of a geometric complex is a star immersion of every class `Cⁿ`. -/
theorem isStarImmersion_realizationToAmbient :
    TauCeti.IsStarImmersion n K.realizationToAmbient := by
  have h := isStarImmersion_secantMap (n := n) (f := K.realizationToAmbient) (by
    rw [secantMap_realizationToAmbient]
    exact realizationToAmbient_injective)
  rwa [secantMap_realizationToAmbient] at h

/-- Let `σ` be a face of `K`. If `F : V → M` is `Cⁿ` within the closed simplex of `σ`, with a
derivative within it at every point which is injective on the directions of the affine span of
`σ`, then `F` following the comparison map is a `Cⁿ` immersion of the closed simplex of `σ`. -/
theorem isSimplexImmersion_comp_realizationToAmbient_comp_faceInclusion (σ : Face K.vertexScheme)
    {F : V → M}
    (hF : ContMDiffOn 𝓘(ℝ, V) I n F
      (convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set V)))
    (hF' : ∀ x ∈ convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set V),
      ∃ F' : V →L[ℝ] E,
        HasMFDerivWithinAt 𝓘(ℝ, V) I F
          (convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set V)) x F' ∧
        ∀ v ∈ vectorSpan ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set V),
          F' v = 0 → v = 0) :
    TauCeti.IsSimplexImmersion I n
      (F ∘ K.realizationToAmbient ∘ faceInclusion K.vertexScheme σ) := by
  rw [← range_vertexScheme_face_coe] at hF hF'
  simpa only [comp_def, realizationToAmbient_faceInclusion] using
    TauCeti.isSimplexImmersion_comp_linearCombination (affineIndependent_vertexScheme_face σ)
      hF hF'

/-- **Smooth triangulations from rectilinear polyhedra.** Let `K` be a geometric simplicial
complex in `V` whose closed simplices form a locally finite family in `K.space`, and let
`f : K.space ≃ₜ M` be a homeomorphism onto a manifold. If on each closed simplex `f` agrees
with a map `F : V → M` which is `Cⁿ` within that simplex, with a derivative injective along its
affine span, then `f` composed with the homeomorphism
`|K.vertexScheme| ≃ₜ K.space` is a `Cⁿ` triangulation of `M`. -/
theorem isSmoothTriangulation_realizationHomeomorph_trans
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → V) ⁻¹' convexHull ℝ (s : Set V))
    (f : K.space ≃ₜ M)
    (hF : ∀ (s : Finset V) (hs : s ∈ K.faces), ∃ F : V → M,
      (∀ (x : V) (hx : x ∈ convexHull ℝ (s : Set V)),
        F x = f ⟨x, convexHull_subset_space hs hx⟩) ∧
      ContMDiffOn 𝓘(ℝ, V) I n F (convexHull ℝ (s : Set V)) ∧
      ∀ x ∈ convexHull ℝ (s : Set V), ∃ F' : V →L[ℝ] E,
        HasMFDerivWithinAt 𝓘(ℝ, V) I F (convexHull ℝ (s : Set V)) x F' ∧
          ∀ v ∈ vectorSpan ℝ (s : Set V), F' v = 0 → v = 0) :
    TauCeti.IsSmoothTriangulation I n ((K.realizationHomeomorph hK).trans f) := by
  refine TauCeti.isSmoothTriangulation_iff.mpr fun σ => ?_
  obtain ⟨F, hFf, hFs, hF'⟩ := hF _ (mem_vertexScheme_iff.mp σ.property)
  have h : (K.realizationHomeomorph hK).trans f ∘ faceInclusion K.vertexScheme σ =
      F ∘ K.realizationToAmbient ∘ faceInclusion K.vertexScheme σ := by
    funext y
    simp only [comp_apply, Homeomorph.trans_apply]
    have hmem : K.realizationToAmbient (faceInclusion _ σ y) ∈
        convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set V) := by
      rw [← range_realizationToAmbient_comp_faceInclusion σ]
      exact mem_range_self y
    rw [hFf _ hmem]
    exact congrArg f (Subtype.ext (coe_realizationHomeomorph_apply hK _))
  rw [h]
  exact isSimplexImmersion_comp_realizationToAmbient_comp_faceInclusion σ
    hFs hF'

end Geometry.SimplicialComplex
