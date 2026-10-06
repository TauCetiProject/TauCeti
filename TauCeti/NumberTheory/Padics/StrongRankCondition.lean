/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Strong rank condition for the `p`-adic numbers

The strong rank condition supports the basis and dimension APIs for modules over `ℚ_[p]`.

## Main declarations

* `TauCeti.instStrongRankConditionPadic`: a direct instance of the strong rank condition for
  `ℚ_[p]`.

## Implementation notes

The priority selects the field's direct nontriviality witness before instance search tries
module-derived nontriviality instances. The proof uses Mathlib's
`commRing_strongRankCondition`.
-/

public section

namespace TauCeti

/-- A direct rank-condition witness for a `p`-adic field avoids searching through
module-derived nontriviality instances. -/
instance (priority := 1100) instStrongRankConditionPadic (p : ℕ) [Fact p.Prime] :
    StrongRankCondition ℚ_[p] := by
  let hfield : Field ℚ_[p] := @NormedField.toField _ (Padic.normedField p)
  exact @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)

end TauCeti
