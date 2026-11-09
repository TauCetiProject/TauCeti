/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Simplex
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import TauCeti.Analysis.Convex.SimplicialComplex.Arrangement
import TauCeti.Topology.PL.Compact

/-!
# Piecewise-linear maps on geometric simplicial complexes

A map which agrees with a continuous affine map on each simplex of a locally finite
geometric simplicial complex is piecewise linear. Local finiteness is needed only along
the subset on which the map is being considered. The target can be any real topological
vector space.

This connects simplicial presentations of maps with the local polyhedral predicate `IsPLOn`
used for PL transition maps. Simplices of every dimension, including those of positive
codimension in the ambient space, are legitimate polyhedral cells.

Conversely, a PL map on the polyhedron of a finite complex `K` is affine on every simplex of
some finite subdivision of `K` (`TauCeti.IsPLOn.exists_isSubdivision_eqOn`): its finitely many
affine pieces live on convex polyhedra, and `K` is subdivided so that each simplex lies in a
polyhedron its open simplex meets
(`Geometry.SimplicialComplex.exists_isSubdivision_convexHull_subset_of_inter_nonempty`). So a map
on a compact polyhedron is PL exactly when it is simplicial for some triangulation
(`Geometry.SimplicialComplex.isPLOn_space_iff_exists_isSubdivision`). With an injective map this
triangulates its image (`Geometry.SimplicialComplex.map`).

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


variable {K : SimplicialComplex ℝ E} {f : E → F}

/-- **A PL map is affine on the simplices of a subdivision.** A map which is piecewise linear on
the polyhedron of a finite geometric simplicial complex `K` agrees with a continuous affine map on
each simplex of some finite subdivision of `K`. -/
theorem _root_.TauCeti.IsPLOn.exists_isSubdivision_eqOn (hf : IsPLOn f K.space)
    (hK : K.faces.Finite) :
    ∃ K' : SimplicialComplex ℝ E, K'.IsSubdivision K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∃ A : E →ᴬ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
  have hcpt : IsCompact K.space := by
    rw [space]
    exact hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨n, C, A, hC, hcov, heq⟩ :=
    isPiecewiseAffineOn_iff.1 (hf.isPiecewiseAffineOn_of_isCompact_of_finiteDimensional hcpt)
  obtain ⟨K', hK'K, hK'f, hsub⟩ := exists_isSubdivision_convexHull_subset_of_inter_nonempty hK hC
  refine ⟨K', hK'K, hK'f, fun s hs => ?_⟩
  -- A point of the open simplex lies in some cell `C j`; then the whole simplex does.
  have hsK : convexHull ℝ (s : Set E) ⊆ K.space :=
    hK'K.space_eq ▸ convexHull_subset_space hs
  obtain ⟨x, hx⟩ := ((Finset.coe_nonempty.2 (K'.nonempty_of_mem_faces hs)).convexHull
    (𝕜 := ℝ)).intrinsicInterior (convex_convexHull ℝ _)
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov (hsK (intrinsicInterior_subset hx)))
  exact ⟨A j, (heq j).mono (subset_inter hsK (hsub s hs j ⟨x, hx, hj⟩))⟩

/-- **PL maps on a compact polyhedron are the simplicial ones.** A map on the polyhedron of a
finite geometric simplicial complex `K` is piecewise linear exactly when it agrees with a
continuous affine map on each simplex of some finite subdivision of `K`. -/
theorem isPLOn_space_iff_exists_isSubdivision (hK : K.faces.Finite) :
    IsPLOn f K.space ↔ ∃ K' : SimplicialComplex ℝ E, K'.IsSubdivision K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∃ A : E →ᴬ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
  refine ⟨fun hf => hf.exists_isSubdivision_eqOn hK, fun ⟨K', hK'K, hK'f, hA⟩ => ?_⟩
  choose A hA using fun s : K'.faces => hA s.1 s.2
  have : Finite K'.faces := hK'f.to_subtype
  exact K'.isPLOn_of_locallyFinite hK'K.space_eq.ge
    (fun _ _ => ⟨univ, univ_mem, Set.toFinite _⟩) A fun s => (hA s).mono inter_subset_right

end Geometry.SimplicialComplex
