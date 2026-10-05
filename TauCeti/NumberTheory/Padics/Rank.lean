/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The strong rank condition over a p-adic field

The p-adic field satisfies the strong rank condition via its canonical normed-field structure.
The direct instance keeps rank computations under scalar extension from searching for alternative
ring structures.
-/

public section

namespace TauCeti.Padic

/-- A p-adic field satisfies the strong rank condition. -/
instance instStrongRankCondition (p : ℕ) [Fact p.Prime] : StrongRankCondition ℚ_[p] := by
  let hfield : Field ℚ_[p] := @NormedField.toField _ (_root_.Padic.normedField p)
  exact @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)

end TauCeti.Padic
