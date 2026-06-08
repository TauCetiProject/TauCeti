/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf algebras

This file records a small API for scalar extension of Hopf algebras.  Mathlib already supplies
the Hopf algebra structure on a tensor product of Hopf algebras; specializing one factor to the
base ring gives the scalar extension `S ⊗[R] A` of an `R`-Hopf algebra `A` along `R → S`.

The reductive-groups roadmap needs this form of base change in Layer 0, both for changing the
base field of an affine group scheme and for comparing functors of points before and after base
change.  The facts here keep the construction explicit: the scalar-extended antipode and counit
are described on pure tensors.  The underlying canonical inclusion and the tensor-product
adjunction are Mathlib's `Algebra.TensorProduct.includeRight` and `AlgHom.liftEquiv`.

## Main declarations

* `HopfAlgebra.BaseChange`: the scalar extension `S ⊗[R] A` of an `R`-Hopf algebra.
* `HopfAlgebra.baseChange_antipode_tmul`: the scalar-extended antipode on a pure tensor.
* `HopfAlgebra.baseChange_counit_tmul`: the scalar-extended counit on a pure tensor.

## References

This supports the "Base change. `K ⊗[k] A` as a Hopf algebra over `K`" item in Layer 0 of the
Tau Ceti reductive-groups roadmap.  The underlying tensor-product Hopf algebra instance is due to
Amelia Livingston and Andrew Yang in Mathlib.
-/

open Coalgebra TensorProduct
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The scalar extension of an `R`-algebra `A` along `R → S`.  When `A` is a Hopf algebra over
`R`, Mathlib's tensor-product Hopf algebra instance equips this algebra with a Hopf algebra
structure over `S`. -/
abbrev BaseChange [Semiring A] [Algebra R A] :=
  S ⊗[R] A

variable [Semiring A] [_root_.HopfAlgebra R A]

/-- The antipode on the scalar extension is obtained by extending the antipode on `A` and using
the identity antipode on the base ring. -/
@[simp]
lemma baseChange_antipode_tmul (s : S) (a : A) :
    _root_.HopfAlgebraStruct.antipode S (A := BaseChange R S A) (s ⊗ₜ[R] a) =
      s ⊗ₜ[R] _root_.HopfAlgebraStruct.antipode R a := by
  simp [BaseChange]

/-- The counit of the scalar extension sends a pure tensor `s ⊗ a` to
`s * algebraMap R S (ε a)`. -/
@[simp]
lemma baseChange_counit_tmul (s : S) (a : A) :
    counit (R := S) (A := BaseChange R S A) (s ⊗ₜ[R] a) =
      s * algebraMap R S (counit (R := R) a) := by
  simp [BaseChange, Algebra.smul_def, mul_comm]

/-- The comultiplication of the scalar extension on a pure tensor, stated directly in terms of
Mathlib's tensor-product coalgebra structure. -/
@[simp]
lemma baseChange_comul_tmul (s : S) (a : A) :
    comul (R := S) (A := BaseChange R S A) (s ⊗ₜ[R] a) =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A
        (comul (R := S) s ⊗ₜ[R] comul (R := R) a) := by
  rfl

/-- The scalar-extended counit after the canonical inclusion is the original counit followed by
the base map. -/
@[simp]
lemma baseChange_counit_includeRight (a : A) :
    counit (R := S) (A := BaseChange R S A)
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A) a) =
      algebraMap R S (counit (R := R) a) := by
  simp [Algebra.smul_def]

/-- The scalar-extended antipode after the canonical inclusion is the canonical inclusion after
the original antipode. -/
@[simp]
lemma baseChange_antipode_includeRight (a : A) :
    _root_.HopfAlgebraStruct.antipode S (A := BaseChange R S A)
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A) a) =
      Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)
        (_root_.HopfAlgebraStruct.antipode R a) := by
  simp

end HopfAlgebra

end TauCeti
