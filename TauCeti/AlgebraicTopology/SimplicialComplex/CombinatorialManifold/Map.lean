/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
import TauCeti.Data.Finset.Card

/-!
# Relabeling combinatorial balls, spheres, and manifolds

An injective map of ambient vertex types preserves combinatorial balls, spheres, and manifolds of
any dimension, and already reflects combinatorial balls via finite-support stellar transport
(`StellarEquivalentUpToRelabeling.of_map`). Reflecting combinatorial spheres (and hence manifolds)
requires sphere–ball disjointness (`IsCombinatorialSphere.not_isCombinatorialBall`) and is proved
in `CombinatorialManifold.Relabel`.

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
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) := by
    rw [← dimension_map_of_injective f hf, h.dimension_eq]
  obtain ⟨V, -, hVcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  obtain ⟨W, hWcard, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨g, hg, hVimg⟩ := Finset.exists_injective_image_eq hf (hVcard.trans hWcard.symm)
  rw [← hVimg, ← map_simplex] at he
  exact isCombinatorialBall_iff.mpr ⟨V, hVcard,
    StellarEquivalentUpToRelabeling.of_map hKfin hf hg he⟩

/-- Injective relabeling preserves and reflects combinatorial balls. -/
@[simp]
theorem isCombinatorialBall_map_iff (f : ι → κ) (hf : Function.Injective f) :
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

/-- Injectively relabeling a combinatorial manifold gives a combinatorial manifold of the same
dimension. -/
theorem IsCombinatorialManifold.map (h : IsCombinatorialManifold K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialManifold (K.map f) n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hw
    rw [← Finset.image_singleton, ← map_link f hf, isCombinatorialManifold_zero_iff.mp h hv,
      map_bot]
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hw
    rw [← Finset.image_singleton, ← map_link f hf]
    exact (isCombinatorialManifold_succ_iff.mp h hv).imp
      (fun hs => hs.map f hf) (fun hb => hb.map f hf)

end PreAbstractSimplicialComplex
