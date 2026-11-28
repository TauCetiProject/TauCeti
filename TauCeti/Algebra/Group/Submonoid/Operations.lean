/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations

/-!
# Coercions under equality of submonoids

The equivalence induced by equality of submonoids preserves the ambient value in both
directions. The additive statements apply to equality of additive submonoids.
-/

public section

namespace MulEquiv

variable {M : Type*} [Monoid M] {S T : Submonoid M}

/-- The equivalence induced by equality of submonoids preserves ambient values. -/
@[to_additive (attr := simp)
  /-- The equivalence induced by equality of additive submonoids preserves ambient values. -/]
theorem submonoidCongr_apply (h : S = T) (x : S) :
    ((submonoidCongr h) x : M) = x := by
  subst h
  rfl

/-- The inverse equivalence induced by equality of submonoids preserves ambient values. -/
@[to_additive (attr := simp)
  /-- The inverse equivalence induced by equality of additive submonoids preserves ambient
  values. -/]
theorem submonoidCongr_symm_apply (h : S = T) (x : T) :
    ((submonoidCongr h).symm x : M) = x := by
  subst h
  rfl

end MulEquiv
