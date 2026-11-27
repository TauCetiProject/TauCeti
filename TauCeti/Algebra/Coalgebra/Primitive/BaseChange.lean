/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# Base change of skew-primitive elements

If `a` is a `(g, h)`-skew-primitive element of an `R`-coalgebra `C`, then `1 ⊗ a` is a
`(1 ⊗ g, 1 ⊗ h)`-skew-primitive element of the scalar extension `A ⊗[R] C`, for any commutative
`R`-algebra `A`. In particular primitive elements of a bialgebra stay primitive after extension
of scalars. No flatness is needed.

## Main declarations

* `Coalgebra.IsSkewPrimitiveElem.one_tmul`: base change of a skew-primitive element.
* `Bialgebra.IsPrimitiveElem.one_tmul`: base change of a primitive element.
-/

public section

open scoped TensorProduct

variable {R A C : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

namespace Coalgebra.IsSkewPrimitiveElem

variable [AddCommMonoid C] [Module R C] [Coalgebra R C] {g h a : C}

/-- A `(g, h)`-skew-primitive element `a` of an `R`-coalgebra gives the
`(1 ⊗ g, 1 ⊗ h)`-skew-primitive element `1 ⊗ a` of its scalar extension. -/
theorem one_tmul (ha : IsSkewPrimitiveElem R g h a) :
    IsSkewPrimitiveElem A ((1 : A) ⊗ₜ[R] g) ((1 : A) ⊗ₜ[R] h) ((1 : A) ⊗ₜ[R] a) where
  counit_eq_zero := by simp [ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    rw [TauCeti.Coalgebra.baseChange_comul_tmul, ha.comul_eq_tmul_add_tmul,
      TensorProduct.tmul_add, map_add,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

end Coalgebra.IsSkewPrimitiveElem

namespace Bialgebra.IsPrimitiveElem

variable [Semiring C] [Bialgebra R C] {a : C}

/-- A primitive element `a` of an `R`-bialgebra gives the primitive element `1 ⊗ a` of its scalar
extension. -/
theorem one_tmul (ha : IsPrimitiveElem R a) : IsPrimitiveElem A ((1 : A) ⊗ₜ[R] a) :=
  Coalgebra.IsSkewPrimitiveElem.one_tmul ha

end Bialgebra.IsPrimitiveElem
