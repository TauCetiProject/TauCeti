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
# Modules over a commutative ring as symmetric bimodules

The ring structure of a trivial square-zero extension `TrivSqZeroExt R M` uses a right action of
`R` on `M`, that is a `Module Rᵐᵒᵖ M` instance. When `R` is commutative, any `R`-module `M` has
one agreeing with the left action. This file provides it as the definition
`TauCeti.TrivSqZeroExt.moduleMulOpposite`, not an instance, since `M` may already carry another
right action, together with the fact `TauCeti.TrivSqZeroExt.isCentralScalar_moduleMulOpposite`
that the two actions agree.

Mathlib provides no right action of `ℤ` on `ZMod n`, so the file also makes these scoped
instances for `R = ℤ` and `M = ZMod n` in the namespace `TauCeti.TrivSqZeroExt`:
`open scoped TauCeti.TrivSqZeroExt` makes `TrivSqZeroExt ℤ (ZMod n)` a commutative ring and a
`ℤ`-algebra.

## Main definitions

* `TauCeti.TrivSqZeroExt.moduleMulOpposite`: the right action of a commutative semiring `R` on an
  `R`-module, agreeing with the left action.
* `TauCeti.TrivSqZeroExt.moduleIntMulOppositeZMod`: the scoped right action of `ℤ` on `ZMod n`.
* `TauCeti.TrivSqZeroExt.isCentralScalarIntZMod`: the right and left actions of `ℤ` on `ZMod n`
  agree.
-/

public section

namespace TauCeti.TrivSqZeroExt

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The right action of a commutative semiring `R` on an `R`-module `M`, agreeing with the left
action. With it, the trivial square-zero extension `R ⋉ M` is a commutative ring. This is not an
instance, since `M` may already carry a different right action of `R`. -/
abbrev moduleMulOpposite : Module Rᵐᵒᵖ M :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

/-- The right action `moduleMulOpposite` of a commutative semiring `R` on an `R`-module agrees
with the left action. -/
theorem isCentralScalar_moduleMulOpposite :
    letI := moduleMulOpposite R M
    IsCentralScalar R M :=
  letI := moduleMulOpposite R M
  ⟨fun _ _ ↦ rfl⟩

variable (n : ℕ)

/-- The right action of `ℤ` on `ℤ/n`, agreeing with the left action, which makes the trivial
square-zero extension `ℤ ⋉ ℤ/n` a ring. -/
scoped instance moduleIntMulOppositeZMod : Module ℤᵐᵒᵖ (ZMod n) :=
  moduleMulOpposite ℤ (ZMod n)

/-- The right and left actions of `ℤ` on `ℤ/n` agree. -/
scoped instance isCentralScalarIntZMod : IsCentralScalar ℤ (ZMod n) :=
  isCentralScalar_moduleMulOpposite ℤ (ZMod n)

end TauCeti.TrivSqZeroExt
