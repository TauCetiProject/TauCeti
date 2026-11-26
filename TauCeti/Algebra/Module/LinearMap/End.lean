/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Actions as module endomorphisms

Supplements to `Mathlib.Algebra.Module.LinearMap.End`.

## Main results

* `DistribSMul.coe_toLinearMap`: the linear map `DistribSMul.toLinearMap R M s` is, as a
  function, multiplication by `s`.
* `LinearEquiv.isUnit_apply_one`: a linear automorphism of the free module `A` of rank one sends
  `1` to a unit.
-/

public section

namespace DistribSMul

variable (R M : Type*) {S : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DistribSMul S M] [SMulCommClass S R M]

/-- As a function, `DistribSMul.toLinearMap R M s` is multiplication by `s`. This is the
unapplied form of `DistribSMul.toLinearMap_apply`. -/
theorem coe_toLinearMap (s : S) : ⇑(toLinearMap R M s) = fun m : M ↦ s • m :=
  funext (toLinearMap_apply R M s)

end DistribSMul

namespace LinearEquiv

variable {A : Type*} [Semiring A]

/-- A linear automorphism of the free module `A` of rank one sends `1` to a unit. -/
theorem isUnit_apply_one (φ : A ≃ₗ[A] A) : IsUnit (φ 1) :=
  -- `Module.End A A ≃+* Aᵐᵒᵖ` sends an endomorphism to its value at `1`.
  (((Module.End.isUnit_iff φ.toLinearMap).2 φ.bijective).map (RingEquiv.moduleEndSelf A).symm).unop

end LinearEquiv
