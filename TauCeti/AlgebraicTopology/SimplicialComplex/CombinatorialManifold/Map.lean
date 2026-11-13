/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic

/-!
# Relabeling combinatorial balls, spheres, and manifolds

An injective map of ambient vertex types sends a combinatorial ball, sphere, or manifold to one of
the same dimension, and reflects combinatorial balls. This allows local models described using
disjoint tagged vertex types, such as joins, to be compared with the original complexes.

The forward transport uses `StellarEquivalentUpToRelabeling.map`: injectively relabel the stellar
equivalence to a standard simplex (resp. simplex boundary), whose image is again a standard
simplex (resp. simplex boundary) with the same number of vertices. Reflecting a combinatorial ball
uses `StellarEquivalentUpToRelabeling.of_map` together with a top-dimensional face of the source
complex. Reflecting combinatorial spheres and manifolds additionally requires distinguishing balls
from spheres so that the source complex spans at least `n + 2` vertices, and therefore lives in
`CombinatorialManifold.Homotopy`.

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

/-- An injective vertex map reflects combinatorial balls. -/
theorem IsCombinatorialBall.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialBall (K.map f) n) : IsCombinatorialBall K n := by
  obtain ⟨W, hW, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨τ, hτ, hτcard⟩ := exists_face_card_eq_of_dimension_eq h.dimension_eq
  obtain ⟨V, _, rfl⟩ := mem_map_iff.mp hτ
  have hVcard : V.card = n + 1 := by
    rwa [Finset.card_image_of_injective V hf] at hτcard
  have hfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  refine isCombinatorialBall_iff.mpr ⟨V, hVcard, ?_⟩
  apply StellarEquivalentUpToRelabeling.of_map hfin f hf
  rw [map_simplex]
  exact he.trans (stellarEquivalentUpToRelabeling_simplex_of_card_eq (hW.trans hτcard.symm))

/-- An injective vertex map preserves and reflects combinatorial balls. -/
theorem IsCombinatorialBall.map_iff_of_injective (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialBall (K.map f) n ↔ IsCombinatorialBall K n :=
  ⟨IsCombinatorialBall.of_map f hf, fun h => h.map f hf⟩

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

/-- Injectively relabeling a combinatorial manifold preserves its dimension and manifold
structure. -/
theorem IsCombinatorialManifold.map (h : IsCombinatorialManifold K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialManifold (K.map f) n := by
  cases n with
  | zero =>
      refine isCombinatorialManifold_zero_iff.mpr fun _ hy => ?_
      obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hy
      rw [← Finset.image_singleton f v, ← map_link f hf, isCombinatorialManifold_zero_iff.mp h hv,
        map_bot]
  | succ n =>
      refine isCombinatorialManifold_succ_iff.mpr fun _ hy => ?_
      obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hy
      rw [← Finset.image_singleton f v, ← map_link f hf]
      exact (isCombinatorialManifold_succ_iff.mp h hv).imp
        (fun hs => hs.map f hf) (fun hb => hb.map f hf)

end PreAbstractSimplicialComplex
