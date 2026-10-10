/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Basic instances for the `p`-adic numbers

This file provides a direct instance for the nontriviality of `ℚ_[p]`, already implied by
its field structure, and an instance expressing that `2` is invertible. These instances support
finite-dimensional constructions and algebraic trace and norm calculations over the `p`-adic field.
-/

public section

noncomputable section

namespace TauCeti

/-- A direct instance of the existing fact that the `p`-adic field has distinct zero and one. -/
-- Avoid backtracking through Henselian-ring instances during rank and freeness synthesis.
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

/-- Two is invertible in the `p`-adic field, including when `p = 2`. -/
instance (p : ℕ) [Fact (Nat.Prime p)] : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

end TauCeti
