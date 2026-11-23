/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic

/-!
# Relabeling combinatorial balls, spheres and manifolds

An injective map of ambient vertex types sends a combinatorial ball, sphere or manifold to a
combinatorial ball, sphere or manifold, respectively, of the same dimension. This allows local
models described using disjoint tagged vertex types, such as joins, to be compared with the
original complexes.

For balls and spheres the transport uses `StellarEquivalentUpToRelabeling.map`: injectively
relabel the stellar equivalence to a standard simplex (resp. simplex boundary), whose image is
again a standard simplex (resp. simplex boundary) with the same number of vertices. For manifolds
it transports each vertex link along the relabeling (`map_link`).

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

/-- Injectively relabeling a combinatorial manifold preserves its dimension and manifold
structure. -/
theorem IsCombinatorialManifold.map (h : IsCombinatorialManifold K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialManifold (K.map f) n := by
  have hlink (x : ι) : link (K.map f) {f x} = (link K {x}).map f := by
    rw [map_link f hf, Finset.image_singleton]
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := singleton_mem_map_iff.mp hy
    rw [hlink, isCombinatorialManifold_zero_iff.mp h hx, map_bot]
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := singleton_mem_map_iff.mp hy
    rw [hlink]
    exact (isCombinatorialManifold_succ_iff.mp h hx).imp (·.map f hf) (·.map f hf)

end PreAbstractSimplicialComplex
