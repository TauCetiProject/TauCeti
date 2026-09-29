/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Trivial actions

A trivial action of `G` on `R`, `g • m = m` for all `g` and `m`, given as a hypothesis rather than
as an instance: this is how the trivial coefficient modules of group cohomology are handled, where
the action of `G` on a ring of coefficients is a parameter and its triviality a hypothesis
(`TauCeti.cohomFpAddEquivH1`).

## Main results

* `TauCeti.smul_mul_smul_of_smul_eq_self`: for a trivial action on a multiplicative structure,
  multiplication is equivariant, `g • m * g • n = g • (m * n)`.
-/

public section

namespace TauCeti

variable {G : Type*} {R : Type*} [Mul R] [SMul G R]

/-- For a trivial action of `G` on a multiplicative structure, multiplication is equivariant. -/
theorem smul_mul_smul_of_smul_eq_self (htriv : ∀ (g : G) (m : R), g • m = m) (g : G) (m n : R) :
    g • m * g • n = g • (m * n) := by
  rw [htriv, htriv, htriv]

end TauCeti
