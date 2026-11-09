/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Maps and homeomorphisms between standard simplices

An equivalence of vertex types induces `Equiv.stdSimplexHomeomorph`, preserving
barycentric weights under reindexing. No finiteness assumption on the vertex types is needed.

An affine map `Convexity.StdSimplex.affineMapMk v` out of a standard simplex is determined by the
images `v m` of the vertices. When the source has finitely many vertices and the target is a
standard simplex, the weights of the image of `w` are the bilinear expressions
`∑ m, w.weights m * (v m).weights n`. Every affine map between standard simplices is continuous,
with no finiteness assumption on the vertex types; `Convexity.StdSimplex.continuousAffineMapMk`
bundles it as a continuous map. This makes affine simplices, such as the simplices of a
barycentric subdivision, available as continuous maps between topological standard simplices.

A standard simplex over a Hausdorff ring is Hausdorff (`Convexity.StdSimplex.t2Space`), so
continuous surjections onto it from compact spaces are quotient maps.
-/

public section

namespace Convexity.StdSimplex

variable {R : Type*} [PartialOrder R] {M N : Type*}

section Semiring

variable [Semiring R] [IsStrictOrderedRing R]

/-- The weights of the affine map with vertices `v`, evaluated at a point with finitely many
vertices, are the corresponding convex combinations of the weights of the vertices. -/
@[simp]
lemma weights_affineMapMk_apply [Fintype M] (v : M → StdSimplex R N) (w : StdSimplex R M)
    (n : N) :
    (affineMapMk v w).weights n = ∑ m, w.weights m * (v m).weights n := by
  simp [affineMapMk_apply, iConvexComb, Finsupp.sum_mapDomain_index, add_smul,
    Finsupp.sum_fintype]

end Semiring

variable [Ring R] [IsStrictOrderedRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- An equivalence of vertex types induces a homeomorphism of standard simplices,
with inverse induced by the inverse equivalence. -/
noncomputable def _root_.Equiv.stdSimplexHomeomorph (e : M ≃ N) :
    StdSimplex R M ≃ₜ StdSimplex R N where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    rw [← map_comp, Equiv.symm_comp_self, map_id]
  right_inv x := by
    rw [← map_comp, Equiv.self_comp_symm, map_id]
  continuous_toFun := continuous_map R e
  continuous_invFun := continuous_map R e.symm

/-- The simplex reindexing homeomorphism acts by Mathlib's standard simplex map. -/
@[simp]
lemma _root_.Equiv.coe_stdSimplexHomeomorph (e : M ≃ N) :
    ⇑(e.stdSimplexHomeomorph (R := R)) = map e := (rfl)

/-- Inverting the simplex reindexing homeomorphism inverts the vertex equivalence. -/
@[simp]
lemma _root_.Equiv.stdSimplexHomeomorph_symm (e : M ≃ N) :
    (e.stdSimplexHomeomorph (R := R)).symm = e.symm.stdSimplexHomeomorph := (rfl)

/-- An affine map between standard simplices is continuous. -/
lemma continuous_affineMapMk (v : M → StdSimplex R N) :
    Continuous (affineMapMk (R := R) v) := by
  classical
  rw [continuous_iff]
  intro ι _ g
  have := Fintype.ofFinite ι
  -- The finitely many vertices `v (g i)` are supported in a finite set `S` of vertices of the
  -- target, so the restricted map factors through the finite standard simplex on `S`.
  let S : Finset N := Finset.univ.biUnion fun i ↦ (v (g i)).weights.support
  have hS (i : ι) : v (g i) ∈ Set.range (map ((↑) : S → N)) := by
    refine (mem_range_map_iff _ _).2 fun n hn ↦ by_contra fun h ↦ hn ⟨⟨n, ?_⟩, rfl⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩
  choose u hu using hS
  have hcomp : ⇑(affineMapMk (R := R) v) ∘ map g = map (↑) ∘ affineMapMk u := by
    funext w
    simp [affineMapMk_apply, map_iConvexComb, hu]
  rw [hcomp]
  refine (continuous_map R _).comp ?_
  rw [(isEmbedding_toFun_comp_weights R S).continuous_iff, continuous_pi_iff]
  intro n
  simp only [Function.comp_def, weights_affineMapMk_apply]
  fun_prop

/-- The affine map with vertices `v` between standard simplices, as a continuous map. -/
noncomputable def continuousAffineMapMk (v : M → StdSimplex R N) :
    C(StdSimplex R M, StdSimplex R N) :=
  ⟨affineMapMk v, continuous_affineMapMk v⟩

@[simp]
lemma continuousAffineMapMk_apply (v : M → StdSimplex R N) (w : StdSimplex R M) :
    continuousAffineMapMk v w = affineMapMk v w := (rfl)

/-- A standard simplex over a Hausdorff ring is Hausdorff. -/
instance t2Space [T2Space R] : T2Space (StdSimplex R N) :=
  .of_injective_continuous (f := fun t : StdSimplex R N ↦ ⇑t.weights)
    (fun _ _ h ↦ ext (DFunLike.coe_injective h)) (continuous_pi (continuous_weights_apply R))

end Convexity.StdSimplex
