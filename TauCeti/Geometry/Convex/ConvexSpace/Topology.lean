/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

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

The facet of the standard simplex `Δⁿ⁺¹` opposite the vertex `j` is included by
`Convexity.StdSimplex.faceInclusion j : C(Δⁿ, Δⁿ⁺¹)`, the vertex map `j.succAbove`, and composites
of facet inclusions agree when the composites of their vertex maps do
(`Convexity.StdSimplex.faceInclusion_comp_faceInclusion`).

The prefix sums `TauCeti.prefixSum N x.weights` of the weights depend continuously on a point `x`
of `StdSimplex R (Fin n)` (`Convexity.StdSimplex.continuous_prefixSum_weights`).

The unconditional series sum of the weights of a point of `StdSimplex R α` equals `1`
(`Convexity.StdSimplex.tsum_weights`).

A standard simplex over a Hausdorff ring is Hausdorff (`Convexity.StdSimplex.t2Space`), so
continuous surjections onto it from compact spaces are quotient maps. Over a finite vertex type, a
standard simplex over a (pseudo)metrizable ring is (pseudo)metrizable
(`Convexity.StdSimplex.pseudoMetrizableSpace`).
-/

public section

namespace Convexity.StdSimplex

/-- The weights of a point of a standard simplex have series sum `1`. -/
@[simp]
theorem tsum_weights {R α : Type*} [LE R] [AddCommMonoid R] [One R] [TopologicalSpace R]
    (s : StdSimplex R α) : ∑' a, s.weights a = 1 :=
  (tsum_eq_sum fun _ ha ↦ Finsupp.notMem_support_iff.mp ha).trans s.total

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

/-- The prefix sums of the weights of a continuously varying point of a standard simplex on
`Fin n` vary continuously. -/
@[fun_prop]
lemma continuous_prefixSum_weights {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    {f : Z → StdSimplex R (Fin n)} (hf : Continuous f) (N : ℕ) :
    Continuous fun z ↦ TauCeti.prefixSum N (f z).weights := by
  simp only [TauCeti.prefixSum_def]
  exact continuous_finsetSum _ fun j _ ↦ (continuous_weights_apply R j).comp hf

/-- A standard simplex over a Hausdorff ring is Hausdorff. -/
instance t2Space [T2Space R] : T2Space (StdSimplex R N) :=
  .of_injective_continuous (f := fun t : StdSimplex R N ↦ ⇑t.weights)
    (fun _ _ h ↦ ext (DFunLike.coe_injective h)) (continuous_pi (continuous_weights_apply R))

/-- A standard simplex on a finite type over a pseudometrizable ring is pseudometrizable (and hence
metrizable via `t2Space` whenever `R` is metrizable). -/
instance pseudoMetrizableSpace [Finite M] [TopologicalSpace.PseudoMetrizableSpace R] :
    TopologicalSpace.PseudoMetrizableSpace (StdSimplex R M) :=
  (isEmbedding_toFun_comp_weights R M).isInducing.pseudoMetrizableSpace

section Facets

/-- The inclusion of the facet of the standard simplex opposite the vertex `j`. -/
noncomputable def faceInclusion {n : ℕ} (j : Fin (n + 2)) :
    C(StdSimplex R (Fin (n + 1)), StdSimplex R (Fin (n + 2))) :=
  ⟨map j.succAbove, continuous_map R _⟩

/-- The facet inclusion is the simplex vertex map. -/
@[simp]
lemma faceInclusion_apply {n : ℕ} (j : Fin (n + 2)) (z : StdSimplex R (Fin (n + 1))) :
    faceInclusion j z = z.map j.succAbove :=
  (rfl)

/-- The facet inclusion sends the vertex `k` to the vertex `j.succAbove k`. -/
lemma faceInclusion_single {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) :
    faceInclusion j (single (R := R) k) = single (j.succAbove k) :=
  map_single _ _

/-- Two composites of facet inclusions agree when the composites of the vertex maps do. -/
lemma faceInclusion_comp_faceInclusion {n : ℕ} {i j' : Fin (n + 2)} {j i' : Fin (n + 3)}
    (h : j.succAbove ∘ i.succAbove = i'.succAbove ∘ j'.succAbove) :
    (faceInclusion (R := R) j).comp (faceInclusion i) =
      (faceInclusion i').comp (faceInclusion j') := by
  ext1 z
  simp only [ContinuousMap.comp_apply, faceInclusion_apply, ← map_comp, h]

end Facets

end Convexity.StdSimplex
