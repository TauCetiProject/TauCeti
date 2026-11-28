/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Subdivision
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Basic

/-!
# Comparing simplicial-set and ordered-complex last-vertex maps

On a standard ordered vertex set, the two subdivision constructions send a face
barycenter to the same largest vertex. This identifies their vertex computations.
-/

public section

universe u

open CategoryTheory Opposite Simplicial

namespace AbstractSimplicialComplex

/-- For a face on the lifted standard vertex set, the simplicial-set last-vertex map
agrees with the last-vertex map of the ordered abstract complex at its barycenter. -/
lemma lastVertex_sdVertex_eq_const_lastVertexMap {n : ℕ}
    (K : AbstractSimplicialComplex (ULift.{u} (Fin (n + 1))))
    (τ : TauCeti.SetLike.Face K) :
    (TauCeti.SSet.lastVertex.app Δ[n]).app _
        (TauCeti.SSet.stdSimplex.sdVertex n ⟨τ.val, (K.isRelLowerSet_faces τ.property).1,
          fun i j ↦ le_total i j⟩) =
      SSet.stdSimplex.const n (lastVertexMap K (subdivisionBarycenter K τ)).down (op ⦋0⦌) := by
  rw [PartialOrder.NonemptyFiniteChains.lastVertex_sdVertex, lastVertexMap_subdivisionBarycenter,
    SimplexCategory.lastVertexOrderHom_apply]

end AbstractSimplicialComplex
