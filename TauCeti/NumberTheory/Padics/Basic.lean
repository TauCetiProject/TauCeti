/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Basic instances for the `p`-adic numbers

This file supplies the canonical `Nontrivial ℚ_[p]` instance for prime `p`. It supports
finite-dimensional constructions over the `p`-adic field, including algebraic trace and norm
calculations for finite extensions.
-/

public section

namespace TauCeti

/-- For prime `p`, the `p`-adic field has distinct zero and one. -/
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

end TauCeti
