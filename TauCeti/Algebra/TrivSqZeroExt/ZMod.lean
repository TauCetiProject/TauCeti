/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.ZMod.Defs

/-!
# `ℤ/n` as a symmetric `ℤ`-bimodule

The ring structure of a trivial square-zero extension `TrivSqZeroExt R M` uses a right action of
`R` on `M`, that is a `Module Rᵐᵒᵖ M` instance, which Mathlib does not provide for `R = ℤ` and
`M = ZMod n`. This file supplies it, agreeing with the left action, together with
`IsCentralScalar ℤ (ZMod n)`, as scoped instances in the namespace `TauCeti.TrivSqZeroExt`, so
that `open scoped TauCeti.TrivSqZeroExt` makes `TrivSqZeroExt ℤ (ZMod n)` a commutative ring and a
`ℤ`-algebra.

## Main definitions

* `TauCeti.TrivSqZeroExt.moduleIntMulOppositeZMod`: the right action of `ℤ` on `ZMod n`.
* `TauCeti.TrivSqZeroExt.isCentralScalarIntZMod`: the right and left actions of `ℤ` on `ZMod n`
  agree.
-/

public section

namespace TauCeti.TrivSqZeroExt

variable (n : ℕ)

/-- The right action of `ℤ` on `ℤ/n`, agreeing with the left action, which makes the trivial
square-zero extension `ℤ ⋉ ℤ/n` a ring. -/
scoped instance moduleIntMulOppositeZMod : Module ℤᵐᵒᵖ (ZMod n) :=
  Module.compHom _ ((RingHom.id ℤ).fromOpposite mul_comm)

/-- The right and left actions of `ℤ` on `ℤ/n` agree. -/
scoped instance isCentralScalarIntZMod : IsCentralScalar ℤ (ZMod n) :=
  ⟨fun _ _ ↦ rfl⟩

end TauCeti.TrivSqZeroExt
