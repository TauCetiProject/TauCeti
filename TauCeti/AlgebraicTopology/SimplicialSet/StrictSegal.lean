/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Simplicial operators on strict Segal simplicial sets

In a strict Segal simplicial set, such as the nerve of a category, a simplex is determined by its
spine (Mathlib's `SSet.IsStrictSegal`). Hence a simplicial operator fixes a simplex as soon as it
fixes every edge of its spine.

## Main results

* `SSet.map_eq_of_isStrictSegal`: an `(n + 1)`-simplex whose face opposite to the last vertex is
  constant at a vertex is fixed by any operator that fixes its last edge and collapses the other
  edges of its spine to the vertex `n`.
-/

public section

open CategoryTheory Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

/-- In a strict Segal simplicial set, an `(n + 1)`-simplex whose face opposite to the last vertex
is constant at `x` is fixed by any operator `r` that fixes the last edge and sends every other
edge of the spine to the vertex `n`. -/
theorem map_eq_of_isStrictSegal {n : ℕ} (r : ⦋n + 1⦌ ⟶ ⦋n + 1⦌)
    (hlast : mkOfSucc (Fin.last n) ≫ r = mkOfSucc (Fin.last n))
    (hcast : ∀ j : Fin n, mkOfSucc j.castSucc ≫ r =
      SimplexCategory.const ⦋1⦌ ⦋n⦌ (Fin.last n) ≫ δ (Fin.last (n + 1)))
    {x : X _⦋0⦌} (σ : X _⦋n + 1⦌)
    (hσ : X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) :
    X.map r.op σ = σ := by
  refine (IsStrictSegal.segal (X := X) (n + 1)).injective (Path.ext' fun i ↦ ?_)
  rw [spine_arrow, spine_arrow, ← Functor.map_comp_apply, ← op_comp]
  cases i using Fin.lastCases with
  | last => rw [hlast]
  | cast j =>
    -- Both edges lie in the face opposite to the last vertex, which is constant at `x`.
    rw [hcast, ← mkOfSucc_δ_lt (Fin.castSucc_lt_last _), op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]
    -- `X.δ i` is by definition `X.map (δ i).op`; `change` exposes the face to rewrite with `hσ`.
    change X.map _ (X.δ _ σ) = X.map _ (X.δ _ σ)
    -- Both sides are now pullbacks of the totally degenerate simplex at `x`.
    have key (f : ⦋1⦌ ⟶ ⦋n⦌) : X.map f.op (X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) =
        X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x := by
      rw [← Functor.map_comp_apply, ← op_comp, Subsingleton.elim (f ≫ _)]
    rw [hσ, key, key]

end SSet
