/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Functoriality of simplicial skeletons

Every simplicial map `f : X ⟶ Y` sends each skeleton `X.skeleton n` into the corresponding
skeleton `Y.skeleton n` (`SSet.skeleton_le_preimage_skeleton`).
-/

public section

open CategoryTheory

universe u

namespace SSet

/-- Every simplicial map sends the `n`-skeleton of its domain into the `n`-skeleton of its
codomain. -/
lemma skeleton_le_preimage_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    X.skeleton n ≤ (Y.skeleton n).preimage f := by
  -- Expose the defining supremum of `X.skeleton n` without unfolding the `OrderHom` structure.
  change (⨆ (i : Fin n) (x : X.nonDegenerate i), Subcomplex.ofSimplex x.1) ≤ _
  simp only [iSup_le_iff]
  intro k x
  rw [Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage]
  exact Y.mem_skeleton (f.app _ x.1) k.isLt

end SSet
