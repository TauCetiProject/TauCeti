/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Simplicial identities in truncated simplicial sets

Elementwise forms of the simplicial identities for truncated simplicial sets, complementing
Mathlib's `SSet.δ_comp_σ_self_apply` for untruncated ones.

## Main results

* `SSet.Truncated.δ_zero_comp_σ_zero_apply`: in a truncated simplicial set, the face `δ 0` of the
  degenerate edge `σ 0 x` on a vertex `x` is `x`.
-/

public section

open CategoryTheory Simplicial SimplexCategory.Truncated SimplicialObject.Truncated

universe u

namespace SSet.Truncated

/-- In an `(n + 1)`-truncated simplicial set, the face `δ 0` of the degenerate edge `σ 0 x` on a
vertex `x` is `x`. -/
@[simp]
lemma δ_zero_comp_σ_zero_apply {n : ℕ} (X : SSet.Truncated.{u} (n + 1)) (x : X _⦋0⦌ₙ₊₁) :
    X.map (Hom.tr (SimplexCategory.δ 0)).op (X.map (Hom.tr (SimplexCategory.σ 0)).op x) = x := by
  have fac := SimplexCategory.δ_comp_σ_self (i := (0 : Fin 1))
  dsimp at fac
  simp [← Functor.map_comp_apply, ← op_comp, ← Hom.tr_comp, fac]

end SSet.Truncated
