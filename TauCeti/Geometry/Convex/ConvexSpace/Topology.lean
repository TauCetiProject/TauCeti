/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Continuity of affine maps between standard simplices

An affine map `Convexity.StdSimplex.affineMapMk v` out of a standard simplex is determined by the
images `v m` of the vertices. When the target is a standard simplex on a finite type, its
weights are the bilinear expressions `∑ m, w.weights m * (v m).weights n`, so the map is
continuous; `Convexity.StdSimplex.continuousAffineMapMk` bundles it as a continuous map. This
makes affine simplices, such as the simplices of a barycentric subdivision,
available as continuous maps between topological standard simplices.
-/

public section

namespace Convexity.StdSimplex

variable {R : Type*} [PartialOrder R] {M N : Type*}

section Semiring

variable [Semiring R] [IsStrictOrderedRing R]

/-- The weights of the affine map with vertices `v`, evaluated at a point with finitely many
vertices, are the corresponding convex combinations of the weights of the vertices. -/
lemma weights_affineMapMk_apply [Fintype M] (v : M → StdSimplex R N) (w : StdSimplex R M)
    (n : N) :
    (affineMapMk v w).weights n = ∑ m, w.weights m * (v m).weights n := by
  simp [affineMapMk_apply, iConvexComb, Finsupp.sum_mapDomain_index, add_smul,
    Finsupp.sum_fintype]

end Semiring

variable [Ring R] [IsStrictOrderedRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- An affine map from a standard simplex to a standard simplex on a finite type is
continuous. -/
lemma continuous_affineMapMk [Finite N] (v : M → StdSimplex R N) :
    Continuous (affineMapMk (R := R) v) := by
  rw [continuous_iff]
  intro ι _ g
  have := Fintype.ofFinite ι
  have hcomp : ⇑(affineMapMk (R := R) v) ∘ map g = affineMapMk (v ∘ g) := by
    funext w
    simp [affineMapMk_apply]
  rw [hcomp, (isEmbedding_toFun_comp_weights R N).continuous_iff, continuous_pi_iff]
  intro n
  simp only [Function.comp_def, weights_affineMapMk_apply]
  fun_prop

/-- The affine map with vertices `v` from a standard simplex to a standard simplex on a finite
type, as a continuous map. -/
noncomputable def continuousAffineMapMk [Finite N] (v : M → StdSimplex R N) :
    C(StdSimplex R M, StdSimplex R N) :=
  ⟨affineMapMk v, continuous_affineMapMk v⟩

@[simp]
lemma continuousAffineMapMk_apply [Finite N] (v : M → StdSimplex R N) (w : StdSimplex R M) :
    continuousAffineMapMk v w = affineMapMk v w := (rfl)

end Convexity.StdSimplex
