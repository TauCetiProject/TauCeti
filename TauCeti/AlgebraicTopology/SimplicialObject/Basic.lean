/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Additional face identities for simplicial objects

This file supplements `Mathlib.AlgebraicTopology.SimplicialObject.Basic` with additional
simplicial face identities.
-/

public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Simplicial face identity with successor indices: for `j.succ ≤ i`,
`X.δ i.succ ≫ X.δ j.succ = X.δ j.castSucc.succ ≫ X.δ i`. -/
@[reassoc]
lemma δ_succ_comp_δ_succ {C : Type u} [Category.{v} C] (X : SimplicialObject C) {n : ℕ}
    {i : Fin (n + 2)} {j : Fin (n + 1)} (h : j.succ ≤ i) :
    X.δ i.succ ≫ X.δ j.succ = X.δ j.castSucc.succ ≫ X.δ i := by
  simpa [Fin.castSucc_succ] using X.δ_comp_δ h

end CategoryTheory.SimplicialObject
