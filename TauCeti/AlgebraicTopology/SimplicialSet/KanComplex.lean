/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.SimplexHorn

/-!
# The singular simplicial set of a space is a Kan complex

For a topological space `X`, every horn in the singular simplicial set `TopCat.toSSet.obj X` has a
filler, so `TopCat.toSSet.obj X` is a Kan complex (`TopCat.kanComplex_toSSet_obj`).

By Mathlib's criterion `SSet.KanComplex.iff`, a horn `Λ[n + 1, i] ⟶ TopCat.toSSet.obj X` is a
family of singular `n`-simplices of `X`, one for each face `j ≠ i`, whose faces agree as the
simplicial identities require.  Their underlying continuous maps are then defined on the facets of
the topological horn opposite the vertex `i`, and they agree wherever two of those facets meet,
since two facets meet in a codimension-two face
(`Convexity.StdSimplex.exists_map_succAbove_of_map_succAbove_eq`).  They therefore glue to a
continuous map on the topological horn, and composing with a retraction of the topological
simplex onto its horn extends it to the whole simplex
(`Convexity.StdSimplex.exists_continuousMap_comp_map_succAbove`).  This extension is a singular
`(n + 1)`-simplex filling the horn.

The Kan condition is what makes the combinatorial homotopy groups of the simplicial set
`TopCat.toSSet.obj X` available, to be compared with the homotopy groups of `X`.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  Chapter I, for Kan complexes and the singular complex of a space as the basic example.
-/

public section

universe u

open CategoryTheory Simplicial Convexity

namespace TopCat

/-- The singular simplicial set of a topological space is a Kan complex: a family of singular
simplices forming a horn extends to a singular simplex whose faces are the given ones. -/
instance kanComplex_toSSet_obj (X : TopCat.{u}) : (toSSet.obj X).KanComplex := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  -- The continuous maps underlying the facets of the horn.
  let g : ∀ j : Fin (n + 2), j ≠ i → C(StdSimplex ℝ (Fin (n + 1)), X) :=
    fun j hj => X.toSSetObjEquiv _ (SSet.yonedaEquiv (f j hj))
  -- The maps on the facets agree where two facets meet.
  have key : ∀ j hj k hk (y z : StdSimplex ℝ (Fin (n + 1))), j < k →
      y.map j.succAbove = z.map k.succAbove → g j hj y = g k hk z := by
    intro j hj k hk y z hjk h
    obtain _ | n := n
    · have := Fin.lt_def.1 hjk
      have := Fin.val_ne_of_ne hj
      have := Fin.val_ne_of_ne hk
      omega
    obtain ⟨w, rfl, rfl⟩ := StdSimplex.exists_map_succAbove_of_map_succAbove_eq hjk h
    have := congrArg (fun φ => X.toSSetObjEquiv _ (SSet.yonedaEquiv φ) w)
      (hf.δ_pred_comp j k hj hk hjk)
    simpa [g, SSet.stdSimplex.yonedaEquiv_δ_comp] using this
  have hg : ∀ j hj k hk (y z : StdSimplex ℝ (Fin (n + 1))),
      y.map j.succAbove = z.map k.succAbove → g j hj y = g k hk z := by
    intro j hj k hk y z h
    rcases lt_trichotomy j k with hjk | rfl | hjk
    · exact key j hj k hk y z hjk h
    · rw [StdSimplex.map_injective Fin.succAbove_right_injective h]
    · exact (key k hk j hj z y hjk h.symm).symm
  -- They extend to the simplex, and the extension fills the horn.
  obtain ⟨F, hF⟩ := StdSimplex.exists_continuousMap_comp_map_succAbove i g hg
  refine ⟨SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm F), fun j hj => ?_⟩
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply (X.toSSetObjEquiv _).injective
  ext y
  simpa [g] using DFunLike.congr_fun (hF j hj) y

end TopCat
