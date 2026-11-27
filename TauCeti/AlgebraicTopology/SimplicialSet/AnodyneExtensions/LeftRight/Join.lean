/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex

/-!
# Endpoint joins of boundaries

Joining a boundary inclusion with a vertex gives the right endpoint horn inclusion.

## References

* J. Lurie, *Higher Topos Theory*, §2.1.2.
-/

public section

universe u

open CategoryTheory MorphismProperty Simplicial

namespace SSet

namespace join

variable (n : ℕ)

/-- **The inclusion `∂Δ[n] ⋆ Δ[0] ⟶ Δ[n] ⋆ Δ[0]` is right anodyne**: under
`Δ[n] ⋆ Δ[0] ≅ Δ[n + 0 + 1]`, it is the inclusion of the horn `Λ[n + 0 + 1, n + 1]` opposite to the
last vertex (`SSet.join.preimage_range_map_boundary_ι_id`). -/
lemma rightAnodyneExtensions_map_boundary_ι_id :
    rightAnodyneExtensions (map ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u}))) := by
  have h : rightAnodyneExtensions (Subcomplex.range (map ∂Δ[n].ι (𝟙 (Δ[0] : SSet.{u})))).ι :=
    (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (stdSimplexIso n 0)
      (preimage_range_map_boundary_ι_id n)).2 (rightAnodyneExtensions.horn_ι (Fin.last_pos))
  rw [← Subcomplex.toRange_ι (map ∂Δ[n].ι (𝟙 _))]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) h

end join

end SSet
