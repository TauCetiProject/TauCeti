/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Finite
import Mathlib.Logic.Equiv.Fintype

/-!
# Relabeling combinatorial balls and spheres

This file relates vertex relabelings to intrinsic stellar equivalence and to combinatorial balls and
spheres:

* `stellarEquivalentUpToRelabeling_map_embedding`: relabeling a precomplex along a self-embedding
  `e : ι ↪ ι` preserves its intrinsic stellar equivalence class.
* `stellarEquivalentUpToRelabeling_simplex_of_card_eq` and
  `stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq`: simplices (and simplex boundaries)
  on vertex sets of equal cardinality in a common ambient type are intrinsically stellar equivalent.
* `IsCombinatorialBall.map`, `IsCombinatorialSphere.map`, and `isCombinatorialBall_map_iff`: an
  injective map of ambient vertex types preserves combinatorial balls and spheres of a given
  dimension and reflects combinatorial balls (reflection for combinatorial spheres is proved in
  `CombinatorialManifold.Stellar`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (stellar equivalence, combinatorial balls and spheres).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- Relabeling a complex along any self-embedding `e : ι ↪ ι` yields an intrinsically stellar
equivalent complex. -/
theorem stellarEquivalentUpToRelabeling_map_embedding (K : PreAbstractSimplicialComplex ι)
    (e : ι ↪ ι) : StellarEquivalentUpToRelabeling K (K.map e) := by
  let inl : ι ↪ ι ⊕ ℕ := ⟨Sum.inl, Sum.inl_injective⟩
  exact .of_common_relabeling (e.trans inl) inl
    (by simpa only [Function.Embedding.trans_apply, map_map, Function.comp_def] using .refl _)

/-- Two simplices on vertex sets of the same cardinality are intrinsically stellar equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplex_of_card_eq {V W : Finset ι}
    (hVW : V.card = W.card) : StellarEquivalentUpToRelabeling (simplex V) (simplex W) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq V W hVW
  have himg : V.image e = W := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using he
  simpa only [Equiv.coe_toEmbedding, map_simplex, himg] using
    stellarEquivalentUpToRelabeling_map_embedding (simplex V) e.toEmbedding

/-- Two simplex boundaries on vertex sets of the same cardinality are intrinsically stellar
equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq {V W : Finset ι}
    (hVW : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplexBoundary V) (simplexBoundary W) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq V W hVW
  have himg : V.image e = W := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using he
  have hmap : (simplexBoundary V).map e = simplexBoundary W := by
    simpa only [Equiv.coe_toEmbedding, himg] using map_simplexBoundary V e.toEmbedding
  simpa only [Equiv.coe_toEmbedding, hmap] using
    stellarEquivalentUpToRelabeling_map_embedding (simplexBoundary V) e.toEmbedding

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
