/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Finite

/-!
# Relabeling combinatorial balls and spheres

This file proves that an injective map of ambient vertex types preserves combinatorial balls and
spheres of a given dimension and reflects combinatorial balls (`IsCombinatorialBall.map`,
`IsCombinatorialSphere.map`, and `isCombinatorialBall_map_iff`; reflection for combinatorial spheres
is proved in `CombinatorialManifold.Stellar`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (stellar equivalence, combinatorial balls and spheres).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- Injectively relabeling a combinatorial ball preserves its dimension and ball structure. -/
theorem IsCombinatorialBall.map (h : IsCombinatorialBall K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialBall (K.map f) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  refine isCombinatorialBall_iff.mpr ⟨V.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective V hf, hV]
  · simpa only [map_simplex] using he.map f hf

/-- Injectively relabeling a combinatorial sphere preserves its dimension and sphere structure. -/
theorem IsCombinatorialSphere.map (h : IsCombinatorialSphere K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialSphere (K.map f) n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  refine isCombinatorialSphere_iff.mpr ⟨V.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective V hf, hV]
  · have hmap : (simplexBoundary V).map f = simplexBoundary (V.image f) := by
      simpa only [Function.Embedding.coeFn_mk] using map_simplexBoundary V ⟨f, hf⟩
    rw [← hmap]
    exact he.map f hf

/-- An injective vertex relabeling preserves and reflects combinatorial balls. -/
@[simp]
theorem isCombinatorialBall_map_iff {f : ι → κ} (hf : Function.Injective f) :
    IsCombinatorialBall (K.map f) n ↔ IsCombinatorialBall K n := by
  refine ⟨fun hb => ?_, fun hb => hb.map f hf⟩
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp hb.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) :=
    (dimension_map_of_injective f hf).symm.trans hb.dimension_eq
  obtain ⟨V, _, hVcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  obtain ⟨W, hWcard, heW⟩ := isCombinatorialBall_iff.mp hb
  have hVW : W.card = (V.image f).card := by
    rw [Finset.card_image_of_injective V hf, hVcard, hWcard]
  have heVf : StellarEquivalentUpToRelabeling (K.map f) ((simplex V).map f) := by
    rw [map_simplex]
    exact heW.trans (stellarEquivalentUpToRelabeling_simplex_of_card_eq hVW)
  exact isCombinatorialBall_iff.mpr
    ⟨V, hVcard, (stellarEquivalentUpToRelabeling_map_iff hKfin hf).mp heVf⟩

end PreAbstractSimplicialComplex
