/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Basic facts about monoid algebras

General facts about the monoid algebra `R[G]` that use only its basis elements `single g r`, and
none of the further theory built on it.

## Main results

* `TauCeti.single_sub_one_ne_zero`: over a nontrivial ring, the difference `single g 1 - 1`
  between the basis element at `g` and the unit is nonzero when `g ≠ 1`.
* The `IsMulCommutative (MonoidAlgebra R M)` instance: the monoid algebra of a commutative
  magma over a commutative semiring is commutative, as a mixin on the existing ring structure.

## References

Injectivity of `single` in its index is Mathlib's `MonoidAlgebra.single_left_injective`.
-/

public section

namespace TauCeti

section Commutative

variable {R : Type*} [CommSemiring R] {M : Type*} [Mul M]

/-- The monoid algebra of a commutative magma over a commutative semiring is commutative. This is
the mixin form of Mathlib's `MonoidAlgebra.nonUnitalCommSemiring`, for a multiplication that is
commutative without carrying a `CommSemigroup` instance. -/
instance instIsMulCommutativeMonoidAlgebra [IsMulCommutative M] :
    IsMulCommutative (MonoidAlgebra R M) where
  is_comm.comm f g := by
    have hM := isMulCommutative_iff.mp (inferInstance : IsMulCommutative M)
    simp [MonoidAlgebra.mul_def, Finsupp.sum, mul_comm, hM, f.coeff.support.sum_comm]

end Commutative

variable {R : Type*} [Ring R] {G : Type*} [One G]

/-- Over a nontrivial ring, the difference `single g 1 - 1` between the basis element at `g` and the
unit is nonzero when `g ≠ 1`. -/
theorem single_sub_one_ne_zero [Nontrivial R] {g : G} (hg : g ≠ 1) :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def]
  intro h
  exact hg (MonoidAlgebra.single_left_injective one_ne_zero h)

end TauCeti
