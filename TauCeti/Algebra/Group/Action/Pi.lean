/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pi

/-!
# Commuting actions of a product of monoids on a product

Mathlib's `Pi.smulCommClass'` says that a single scalar type `M` acting on every factor of a
product `∀ i, β i` commutes with the coordinatewise action of `∀ i, α i` when it does so on each
factor. This file adds the same instance with the two scalar types in the other order,
`SMulCommClass (∀ i, α i) M (∀ i, β i)` (`Pi.smulCommClass'''`). Instance search does not derive it
from `Pi.smulCommClass'` by symmetry.

A typical use is the diagonal torus `ι → Circle` acting coordinatewise on `ι → ℂ`: this instance
makes the action commute with complex scalars, so the torus acts on complex subspaces by
`Submodule.pointwiseDistribMulAction`.
-/

public section

namespace Pi

variable {I M : Type*} {α β : I → Type*}

/-- The coordinatewise action of `∀ i, α i` on `∀ i, β i` commutes with an action of `M` on every
factor, when it does so factorwise. This is `Pi.smulCommClass'` with the scalar types exchanged. -/
@[to_additive /-- The coordinatewise action of `∀ i, α i` on `∀ i, β i` commutes with an action of
`M` on every factor, when it does so factorwise. This is `Pi.vaddCommClass'` with the scalar types
exchanged. -/]
instance smulCommClass''' [∀ i, SMul M (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, SMulCommClass (α i) M (β i)] : SMulCommClass (∀ i, α i) M (∀ i, β i) :=
  ⟨fun x y z ↦ funext fun i ↦ smul_comm (x i) y (z i)⟩

end Pi
