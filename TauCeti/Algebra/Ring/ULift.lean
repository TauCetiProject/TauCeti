/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.ULift
public import TauCeti.Algebra.GroupWithZero.ULift

/-!
# `IsDomain` instance for `ULift`

Combining `ULift.isCancelMulZero` and `ULift.nontrivial` makes `ULift R` a domain whenever the
semiring `R` is a domain.
-/

public section

universe u v

namespace ULift

instance isDomain {R : Type u} [Semiring R] [IsDomain R] : IsDomain (ULift.{v} R) where

end ULift
