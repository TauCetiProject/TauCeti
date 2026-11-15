/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.MulAction

/-!
# Scalar actions of `SetLike` structures

The low-priority scalar action on a `SetLike` structure is induced by coercion to its ambient
type. This file exposes the defining equation for general `SetLike` scalar actions.
-/

public section

namespace SetLike

variable {B S α : Type*} [SetLike S B] [SMul B α]

/-- An element of a `SetLike` subtype acts by its coercion to the ambient type. -/
@[to_additive]
theorem coe_smul (C : S) (c : C) (a : α) : c • a = (c : B) • a := (rfl)

end SetLike
