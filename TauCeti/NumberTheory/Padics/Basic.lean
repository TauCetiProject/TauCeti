/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Basic instances for the `p`-adic numbers

A direct nontriviality witness from Mathlib's field structure keeps instance search from
backtracking through Henselian-ring instances. In particular, the rank and freeness instances
used in `p`-adic trace calculations can be synthesized within the default search budget.
-/

public section

namespace TauCeti

/-- The `p`-adic field is nontrivial, directly from Mathlib's field structure. -/
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

end TauCeti
