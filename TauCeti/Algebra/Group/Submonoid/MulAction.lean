/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.MulAction

/-!
# Scalar actions of `SetLike` structures

Mathlib's low-priority scalar action *by* an element of a `SetLike` subtype on another type is
induced by coercion of the element to its ambient type. This file exposes the defining
equation of that action.
-/

public section

namespace TauCeti

variable {B S α : Type*} [SetLike S B] [SMul B α]

/-- An element of a `SetLike` subtype acts by its coercion to the ambient type. -/
@[to_additive]
theorem setLike_smul_def (C : S) (c : C) (a : α) : c • a = (c : B) • a := (rfl)

end TauCeti
