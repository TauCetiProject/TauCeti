/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.Chart
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.ChartedSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Transition

/-!
# PL structures from combinatorial sphere links

If every vertex link of a complex is a combinatorial `n`-sphere, its weak realization
has a PL atlas modeled on `ℝ^(n + 1)`. The charts have exactly the open vertex stars
as their sources. Their PL compatibility follows by composing their ambient forward
and inverse barycentric formulas on overlapping stars.

No finiteness or countability of the ambient complex is required. Each link is finite,
so its closed star supplies the local simplex model. This result concerns sphere links;
manifolds with boundary also require charts at vertices with ball links.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 3 (the PL structure of a combinatorial manifold).
-/

public noncomputable section

open Set TauCeti PreAbstractSimplicialComplex
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
    (fun x : Realization K => (x.1 : ι → ℝ)) ?_⟩
  intro d hd
  rw [starChartedSpace_atlas] at hd
  obtain ⟨v, rfl⟩ := hd
  refine ⟨closedStarRealization K {v}, F v, G v, ?_, ?_, ?_, hf v, hg v⟩
  · rw [hs]
    exact K.openStarRealization_subset_closedStarRealization v
  · simpa only [image_eq_range] using hF v
  · simpa using hG v

end AbstractSimplicialComplex
