/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Simplex
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Piecewise-linear maps on geometric simplicial complexes

A map which agrees with a continuous affine map on each simplex of a locally finite
geometric simplicial complex is piecewise linear. Local finiteness is needed only along
the subset on which the map is being considered. The target can be any real topological
vector space.

This connects simplicial presentations of maps with the local polyhedral predicate `IsPLOn`
used for PL transition maps. Simplices of every dimension, including those of positive
codimension in the ambient space, are legitimate polyhedral cells.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1--2.
-/

public section

open Set Filter Topology TauCeti

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A map affine on the simplices of a geometric complex is PL on any subset of its space
along which the simplex family is locally finite. The affine formulas need agree only on
the traces of the simplices in that subset. -/
theorem isPLOn_of_locallyFinite (K : SimplicialComplex ℝ E) {f : E → F} {s : Set E}
    (hsub : s ⊆ K.space)
    (hlf : ∀ x ∈ s, ∃ U ∈ 𝓝 x,
      {σ : K.faces | (convexHull ℝ (σ.1 : Set E) ∩ U).Nonempty}.Finite)
    (A : K.faces → (E →ᴬ[ℝ] F))
    (heq : ∀ σ, EqOn f (A σ) (s ∩ convexHull ℝ (σ.1 : Set E))) : IsPLOn f s := by
  refine TauCeti.isPLOn_of_locallyFinite hlf
    (fun σ => (K.indep σ.2).isConvexPolyhedron_convexHull) ?_ heq
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.mp (hsub hx)
  exact mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩

end Geometry.SimplicialComplex
