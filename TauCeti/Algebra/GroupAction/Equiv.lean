/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Equivariant equivalences of additive groups

This file records elementary facts about additive equivalences that intertwine group actions.

## Main results

* `TauCeti.AddEquiv.symm_map_smul_of_map_smul`: the inverse of an equivariant additive
  equivalence is equivariant.
-/

public section

namespace TauCeti.AddEquiv

variable {G M N : Type*} [Add M] [Add N] [SMul G M] [SMul G N]

/-- The inverse of an equivariant additive equivalence is equivariant. -/
theorem symm_map_smul_of_map_smul (e : M ≃+ N)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) (n : N) :
    e.symm (g • n) = g • e.symm n := by
  apply e.injective
  rw [e.apply_symm_apply, hequiv, e.apply_symm_apply]

end TauCeti.AddEquiv

end
