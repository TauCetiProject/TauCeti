/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Set

/-!
# Evaluating an order isomorphism restricted to a principal down-set

`OrderIso.Iic` restricts an order isomorphism `e : α ≃o β` to the interval below a point,
`Set.Iic x ≃o Set.Iic (e x)`. It is built as a structure instance, so an application of it does
not rewrite on its own: a consumer that meets `(e.Iic x) y` in a goal has to unfold the
construction to get anywhere.

The two lemmas here supply the missing evaluation rules, in both directions. They hold by `rfl`,
and stating them beside the construction rather than at any use site means no consumer needs the
body of a composite order isomorphism exposed in order to compute with it.
-/

public section

namespace OrderIso

variable {α β : Type*} [Lattice α] [Lattice β]

/-- **Applying a restricted order isomorphism is applying the original.** -/
@[simp]
theorem Iic_apply_coe (e : α ≃o β) (x : α) (y : Set.Iic x) : ((e.Iic x) y : β) = e y :=
  rfl

/-- **Applying the inverse of a restricted order isomorphism is applying the original
inverse.** -/
@[simp]
theorem Iic_symm_apply_coe (e : α ≃o β) (x : α) (y : Set.Iic (e x)) :
    ((e.Iic x).symm y : α) = e.symm y :=
  rfl

end OrderIso

end
