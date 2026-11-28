/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Units.Equiv
/-!
# Units of `ULift` monoids
Transfers `Subsingleton` of `Mˣ` across `ULift` via `MulEquiv.ulift : ULift M ≃* M`, supplying
`Subsingleton (ULift.{u} (ZMod 2))ˣ` for universe-lifted mod-two orientation constructions.
-/
public section
universe u v
instance {M : Type v} [Monoid M] [Subsingleton Mˣ] : Subsingleton (ULift.{u} M)ˣ :=
  (Units.mapEquiv (MulEquiv.ulift : ULift.{u} M ≃* M)).toEquiv.subsingleton
