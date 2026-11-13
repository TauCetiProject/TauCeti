/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Analysis.Normed.Affine.Convex
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Simplicial neighbourhoods

In a finite-dimensional real normed space, every neighbourhood of a point contains the space of a
finite geometric simplicial complex which is itself a neighbourhood of the point
(`Geometry.SimplicialComplex.exists_finite_space_mem_nhds_subset`). The complex consists of one
full-dimensional simplex, containing the point in its interior, together with all of its faces.

This is how local questions about piecewise-linear maps are reduced to finite simplicial
complexes, where subdivision theorems apply.
-/

public section

open Set Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every neighbourhood `U` of a point `x` in a finite-dimensional real normed space contains the
space of a finite geometric simplicial complex which is a neighbourhood of `x`. -/
theorem exists_finite_space_mem_nhds_subset {x : E} {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space ∈ 𝓝 x ∧ K.space ⊆ U := by
  classical
  obtain ⟨b, hx, hsub⟩ := exists_mem_interior_convexHull_affineBasis hU
  let V : Finset E := Finset.univ.image b
  have hV : (V : Set E) = range b := by simp [V]
  have hind : AffineIndependent ℝ ((↑) : ↥(V : Set E) → E) := by
    rw [hV]
    exact b.ind.range
  -- The simplex spanned by the vertices of `b`, with all of its faces.
  let K : SimplicialComplex ℝ E :=
    ofAffineIndependent (PreAbstractSimplicialComplex.simplex V)
      (hind.mono (iUnion₂_subset fun s hs =>
        Finset.coe_subset.2 (PreAbstractSimplicialComplex.mem_simplex.1 hs).2))
  have hspace : K.space = convexHull ℝ (range b) := by
    refine Subset.antisymm (fun y hy => ?_) ?_
    · obtain ⟨s, hs, hys⟩ := mem_space_iff.1 hy
      exact hV ▸ convexHull_mono
        (Finset.coe_subset.2 (PreAbstractSimplicialComplex.mem_simplex.1 hs).2) hys
    · rw [← hV]
      exact convexHull_subset_space (K := K)
        (PreAbstractSimplicialComplex.mem_simplex.2 ⟨Finset.univ_nonempty.image b, subset_rfl⟩)
  refine ⟨K, PreAbstractSimplicialComplex.finite_faces_simplex V, ?_, hspace ▸ hsub⟩
  rw [hspace]
  exact mem_interior_iff_mem_nhds.1 hx

end Geometry.SimplicialComplex
