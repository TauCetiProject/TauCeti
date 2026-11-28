/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.HalfSpace
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.ChartedSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Transition
public import TauCeti.Geometry.Manifold.PLGroupoid.Transport

/-!
# PL structures on combinatorial manifolds

The weak realization of a combinatorial `(n + 1)`-manifold has a PL atlas modelled on the
half-space in `(Fin n → ℝ) × ℝ`. If every vertex link is a combinatorial `n`-sphere, it
also has a PL atlas without boundary, modelled on `ℝ^(n + 1)`. Both atlases are assembled
from charts on the open vertex stars. In the half-space atlas, vertices with sphere links
get charts into the open half-space, and vertices with ball links get charts sending them
to the boundary. PL compatibility follows by composing the ambient forward and inverse
barycentric formulas of the charts on overlapping stars.

No finiteness or countability of the ambient complex is required. Each link is finite,
so its closed star supplies the local simplex model.

Both atlases are then read in Mathlib's models, the Euclidean half-space `𝓡∂ (n + 1)` and the
Euclidean space `𝓡 (n + 1)`, through linear isomorphisms of the model spaces
(`Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`). These are the models of smooth manifolds,
in which the PL structure of a smoothly triangulated manifold is to be compared with its smooth
structure.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 3 (the PL structure of a combinatorial manifold).
-/

public noncomputable section

open AbstractSimplicialComplex Set TauCeti PreAbstractSimplicialComplex
open scoped Manifold

namespace AbstractSimplicialComplex

/-- Sphere links at every vertex give the weak realization a PL structure without boundary.
The atlas is assembled on the existing weak topology, with no global finiteness assumption. -/
theorem exists_chartedSpace_hasGroupoid_of_isCombinatorialSphere_link
    {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) {n : ℕ}
    (h : ∀ v, IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ C : ChartedSpace (Fin (n + 1) → ℝ) (Realization K),
      let := C
      HasGroupoid (Realization K) (PLGroupoid 𝓘(ℝ, Fin (n + 1) → ℝ)) := by
  choose c hs _ _ F G hF hG hf hg using
    fun v => (h v).exists_openPartialHomeomorph_openStar_isPL
  let C := K.starChartedSpace c hs
  let := C
  refine ⟨C, hasGroupoid_PLGroupoid_of_coordinateFormulas
    (fun x : Realization K => (x.val : ι → ℝ)) ?_⟩
  intro d hd
  rw [starChartedSpace_atlas] at hd
  obtain ⟨v, rfl⟩ := hd
  refine ⟨closedStarRealization K {v}, F v, G v, ?_, ?_, ?_, hf v, hg v⟩
  · rw [hs]
    exact K.openStarRealization_subset_closedStarRealization v
  · simpa only [image_eq_range] using hF v
  · simpa using hG v

/-- Sphere links at every vertex give the weak realization a PL structure without boundary,
modelled on Mathlib's Euclidean space `𝓡 (n + 1)`. The atlas is that of
`AbstractSimplicialComplex.exists_chartedSpace_hasGroupoid_of_isCombinatorialSphere_link`
followed by the linear isomorphism `EuclideanSpace.equiv` of the two coordinate spaces. -/
theorem exists_chartedSpace_euclideanSpace_hasGroupoid_of_isCombinatorialSphere_link
    {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) {n : ℕ}
    (h : ∀ v, IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Realization K),
      let := C
      HasGroupoid (Realization K) (PLGroupoid (𝓡 (n + 1))) := by
  obtain ⟨C, hC⟩ := K.exists_chartedSpace_hasGroupoid_of_isCombinatorialSphere_link h
  let := C
  let L := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  refine ⟨_, L.toHomeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp
    (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) ?_ ?_ (Realization K)⟩
  · exact (isPLOn_continuousAffineMap (L : _ →L[ℝ] _).toContinuousAffineMap _).congr
      fun _ _ => by simp
  · exact (isPLOn_continuousAffineMap (L.symm : _ →L[ℝ] _).toContinuousAffineMap _).congr
      fun _ _ => by simp

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

/-- The weak realization of a positive-dimensional combinatorial manifold is a PL manifold,
possibly with boundary: it has an atlas modelled on the half-space in `(Fin n → ℝ) × ℝ` whose
chart transitions lie in the PL groupoid. No finiteness or countability of the complex is
assumed. -/
theorem IsCombinatorialManifold.exists_chartedSpace_hasGroupoid_PLGroupoid
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {n : ℕ}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    ∃ C : ChartedSpace {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} (Realization K),
      let := C
      HasGroupoid (Realization K) (PLGroupoid (modelWithCornersHalfSpace (Fin n → ℝ))) := by
  -- Each vertex has a half-space chart with PL formulas, of the sphere or the ball kind.
  have hchart (v : ι) : ∃ c : OpenPartialHomeomorph (Realization K)
      {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2},
      c.source = openStarRealization K v ∧
      ∃ f : (ι → ℝ) → (Fin n → ℝ) × ℝ, ∃ g : ((Fin n → ℝ) × ℝ) → (ι → ℝ),
        IsPLOn f (range fun x : closedStarRealization K {v} => (x.val.val : ι → ℝ)) ∧
        IsPLOn g ((modelWithCornersHalfSpace (Fin n → ℝ)).symm ⁻¹' c.target ∩
          range (modelWithCornersHalfSpace (Fin n → ℝ))) ∧
        (∀ x ∈ c.source, f (x.val : ι → ℝ) = (c x).val) ∧
        ∀ y ∈ c.target, g y.val = ((c.symm y).val : ι → ℝ) := by
    rcases isCombinatorialManifold_succ_iff.mp h (K.singleton_mem v) with hs | hb
    · obtain ⟨c, hcs, -, hrest⟩ := hs.exists_openPartialHomeomorph_openStar_halfSpace_isPL
      exact ⟨c, hcs, hrest⟩
    · obtain ⟨c, hcs, -, -, hrest⟩ := hb.exists_openPartialHomeomorph_openStar_isPL
      exact ⟨c, hcs, hrest⟩
  choose c hs f g hf hg hfc hgc using hchart
  let C := K.starChartedSpace c hs
  let := C
  refine ⟨C, hasGroupoid_PLGroupoid_of_coordinateFormulas
    (fun x : Realization K => (x.val : ι → ℝ)) ?_⟩
  intro d hd
  rw [starChartedSpace_atlas] at hd
  obtain ⟨v, rfl⟩ := hd
  refine ⟨closedStarRealization K {v}, f v, g v, ?_, ?_, hg v, ?_, ?_⟩
  · rw [hs]
    exact K.openStarRealization_subset_closedStarRealization v
  · simpa only [image_eq_range] using hf v
  · simpa only [modelWithCornersHalfSpace_apply] using hfc v
  · simpa only [modelWithCornersHalfSpace_apply] using hgc v

/-- The weak realization of a positive-dimensional combinatorial manifold is a PL manifold,
possibly with boundary, modelled on Mathlib's Euclidean half-space `𝓡∂ (n + 1)`. The atlas is the
half-space atlas of `IsCombinatorialManifold.exists_chartedSpace_hasGroupoid_PLGroupoid` followed
by the linear isomorphism `(v, t) ↦ (t, v)` of the two half-spaces,
`TauCeti.halfSpaceHomeomorphEuclideanHalfSpace`. -/
theorem IsCombinatorialManifold.exists_chartedSpace_euclideanHalfSpace_hasGroupoid_PLGroupoid
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {n : ℕ}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    ∃ C : ChartedSpace (EuclideanHalfSpace (n + 1)) (Realization K),
      let := C
      HasGroupoid (Realization K) (PLGroupoid (𝓡∂ (n + 1))) := by
  obtain ⟨C, hC⟩ := h.exists_chartedSpace_hasGroupoid_PLGroupoid
  let := C
  exact ⟨_, (halfSpaceHomeomorphEuclideanHalfSpace n).hasGroupoid_PLGroupoid_chartedSpaceComp
    (isPLOn_halfSpaceHomeomorphEuclideanHalfSpace n)
    (isPLOn_halfSpaceHomeomorphEuclideanHalfSpace_symm n) (Realization K)⟩

end PreAbstractSimplicialComplex
