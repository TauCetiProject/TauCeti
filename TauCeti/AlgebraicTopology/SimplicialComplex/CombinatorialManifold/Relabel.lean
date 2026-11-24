/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Relabel

/-!
# Combinatorial balls, spheres and manifolds under injective relabeling

Injective relabelings preserve combinatorial balls, spheres and manifolds
(`CombinatorialManifold.Map`). This file proves that they also reflect them, for an arbitrary
target vertex type. Reflection is what lets a link be recognised as a ball or sphere from a
description after relabeling, such as the description of the link of a new stellar vertex as a
join on a sum type.

The reflection of balls and spheres is `stellarEquivalentUpToRelabeling_map_iff` once a model of
the right size is found in the source type. For balls a top-dimensional face is such a model.
For spheres one more vertex is needed: a complex whose image is a combinatorial `n`-sphere has at
least `n + 2` vertices, since with only `n + 1` it would be a simplex, hence a combinatorial ball,
and a combinatorial sphere is never a combinatorial ball
(`PreAbstractSimplicialComplex.IsCombinatorialSphere.not_isCombinatorialBall`).

## Main results

* `PreAbstractSimplicialComplex.isCombinatorialBall_map_iff` and
  `isCombinatorialSphere_map_iff`: injective relabelings preserve and reflect combinatorial
  balls and spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.of_map` and
  `isCombinatorialManifold_map_iff`: injective relabelings preserve and reflect combinatorial
  manifolds.
-/

public section

open Finset Function

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {K : PreAbstractSimplicialComplex ι}
  {n : ℕ} {f : ι → κ}

/-- A complex whose injective relabeling is a combinatorial ball is a combinatorial ball. -/
theorem IsCombinatorialBall.of_map (hf : Injective f) (h : IsCombinatorialBall (K.map f) n) :
    IsCombinatorialBall K n := by
  obtain ⟨W, hW, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨V, -, hV⟩ := exists_face_card_eq_of_dimension_eq
    ((dimension_map_of_injective f hf).symm.trans h.dimension_eq)
  refine isCombinatorialBall_iff.mpr ⟨V, hV, .of_map hf (he.trans ?_)⟩
  rw [map_simplex]
  exact stellarEquivalentUpToRelabeling_simplex (by rw [hW, card_image_of_injective V hf, hV])

omit [DecidableEq ι] in
/-- A complex whose injective relabeling is a combinatorial `n`-sphere has `n + 2` vertices in its
vertex type: otherwise it would be a simplex. -/
private theorem exists_card_eq_of_isCombinatorialSphere_map (hf : Injective f)
    (h : IsCombinatorialSphere (K.map f) n) : ∃ V : Finset ι, V.card = n + 2 := by
  classical
  by_contra hV
  push Not at hV
  have : Finite ι := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨V, hV'⟩ := Infinite.exists_subset_card_eq ι (n + 2)
    exact hV V hV'
  let := Fintype.ofFinite ι
  have hcard : Fintype.card ι < n + 2 := by
    by_contra hle
    push Not at hle
    obtain ⟨V, -, hV'⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
      (n := n + 2) (by rwa [Finset.card_univ])
    exact hV V hV'
  obtain ⟨σ, hσ, hσcard⟩ := exists_face_card_eq_of_dimension_eq
    ((dimension_map_of_injective f hf).symm.trans h.dimension_eq)
  have hσuniv : σ = Finset.univ :=
    Finset.eq_univ_of_card σ (by have := Finset.card_le_univ σ; omega)
  -- With all vertices in one face, the complex is the simplex on that face.
  have hKσ : K = simplex σ := by
    refine SetLike.ext fun τ => ⟨fun hτ => mem_simplex.mpr ⟨(K.isRelLowerSet_faces hτ).1,
      hσuniv ▸ Finset.subset_univ τ⟩, fun hτ => ?_⟩
    exact (K.isRelLowerSet_faces hσ).2 (mem_simplex.mp hτ).2 (mem_simplex.mp hτ).1
  rw [hKσ, map_simplex] at h
  exact h.not_isCombinatorialBall
    (isCombinatorialBall_simplex (by rw [card_image_of_injective σ hf, hσcard]))

/-- A complex whose injective relabeling is a combinatorial sphere is a combinatorial
sphere. -/
theorem IsCombinatorialSphere.of_map (hf : Injective f) (h : IsCombinatorialSphere (K.map f) n) :
    IsCombinatorialSphere K n := by
  obtain ⟨W, hW, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨V, hV⟩ := exists_card_eq_of_isCombinatorialSphere_map hf h
  refine isCombinatorialSphere_iff.mpr ⟨V, hV, .of_map hf (he.trans ?_)⟩
  have hmap := map_simplexBoundary V ⟨f, hf⟩
  rw [Function.Embedding.coeFn_mk] at hmap
  rw [hmap]
  exact stellarEquivalentUpToRelabeling_simplexBoundary
    (by rw [hW, card_image_of_injective V hf, hV])

/-- Injective relabelings preserve and reflect combinatorial balls. -/
@[simp]
theorem isCombinatorialBall_map_iff (hf : Injective f) :
    IsCombinatorialBall (K.map f) n ↔ IsCombinatorialBall K n :=
  ⟨.of_map hf, fun h => h.map f hf⟩

/-- Injective relabelings preserve and reflect combinatorial spheres. -/
@[simp]
theorem isCombinatorialSphere_map_iff (hf : Injective f) :
    IsCombinatorialSphere (K.map f) n ↔ IsCombinatorialSphere K n :=
  ⟨.of_map hf, fun h => h.map f hf⟩

/-- A complex whose injective relabeling is a combinatorial manifold is a combinatorial
manifold. -/
theorem IsCombinatorialManifold.of_map (hf : Injective f)
    (h : IsCombinatorialManifold (K.map f) n) : IsCombinatorialManifold K n := by
  have hlink (x : ι) : link (K.map f) {f x} = (link K {x}).map f := by
    rw [map_link f hf, Finset.image_singleton]
  have hvert {x : ι} (hx : ({x} : Finset ι) ∈ K) : ({f x} : Finset κ) ∈ K.map f :=
    singleton_mem_map_iff.mpr ⟨x, hx, rfl⟩
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun x hx => ?_
    apply map_injective hf
    simp only [← hlink, isCombinatorialManifold_zero_iff.mp h (hvert hx), map_bot]
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun x hx => ?_
    have hxlink := isCombinatorialManifold_succ_iff.mp h (hvert hx)
    rwa [hlink, isCombinatorialSphere_map_iff hf, isCombinatorialBall_map_iff hf] at hxlink

/-- Injective relabelings preserve and reflect combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_map_iff (hf : Injective f) :
    IsCombinatorialManifold (K.map f) n ↔ IsCombinatorialManifold K n :=
  ⟨.of_map hf, fun h => h.map f hf⟩

end PreAbstractSimplicialComplex
