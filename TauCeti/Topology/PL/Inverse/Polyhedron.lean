/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Simplicial
public import TauCeti.Analysis.Convex.SimplicialComplex.Map

/-!
# Inverses of PL maps on finite polyhedra

A left inverse of a piecewise-linear map on a finite polyhedron is piecewise linear on the
image. No continuity assumption on the inverse is needed. Subdivide the source so that the map
is affine on each simplex, and use the affine inverse on each image simplex.

This applies to polyhedra of arbitrary codimension, without a manifold hypothesis. In particular
it supplies inverse regularity for maps read in the barycentric coordinates of triangulations.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 1–2.
-/

public section

open Set

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {K : Geometry.SimplicialComplex ℝ E} {f : E → F} {g : F → E}

/-- A left inverse of a PL map on a finite polyhedron is PL on its image. The inverse is only
required on the polyhedron; neither continuity nor a right inverse law is assumed. -/
theorem IsPLOn.inverse_of_leftInvOn (hf : IsPLOn f K.space) (hK : K.faces.Finite)
    (hgf : LeftInvOn g f K.space) : IsPLOn g (f '' K.space) := by
  classical
  obtain ⟨L, hLK, hL, hA⟩ := hf.exists_isSubdivision_eqOn hK
  have hinj : InjOn f L.space := hLK.space_eq ▸ hgf.injOn
  have haff : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, hA⟩ := hA s hs
    exact ⟨A.toAffineMap, hA⟩
  let T := L.map f hinj haff
  have hT : T.faces.Finite := Geometry.SimplicialComplex.finite_faces_map_iff.mpr hL
  have hleft : LeftInvOn g f L.space := hLK.space_eq ▸ hgf
  choose B hB using Geometry.SimplicialComplex.simplexwise_affine_of_leftInvOn
    (hf := hinj) (haff := haff) hleft
  have : Finite T.faces := hT.to_subtype
  have hg : IsPLOn g T.space := T.isPLOn_of_locallyFinite subset_rfl
    (fun _ _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩)
    (fun s => ⟨B s.val s.property, (B s.val s.property).continuous_of_finiteDimensional⟩)
    (fun s => (hB s.val s.property).mono inter_subset_right)
  simpa only [T, Geometry.SimplicialComplex.space_map, hLK.space_eq] using hg

end TauCeti
