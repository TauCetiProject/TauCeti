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
change.  This file gives the construction the roadmap-facing name `BaseChange`; the Hopf,
bialgebra, and coalgebra API is Mathlib's tensor-product API, including
`TensorProduct.antipode_def`, `TensorProduct.counit_tmul`, `TensorProduct.comul_tmul`,
`Algebra.TensorProduct.includeRight`, and `AlgHom.liftEquiv`.

## Main declarations

* `HopfAlgebra.BaseChange`: the scalar extension `S ⊗[R] A` of an `R`-algebra, carrying the
  tensor-product Hopf algebra structure when `A` is a Hopf algebra over `R`.
* `HopfAlgebra.BaseChange.inclusion`: the canonical map from `A` into its scalar extension.
* `TauCeti.AlgHom.baseChangeValueEquiv`: algebra-valued points of the base change are
  algebra-valued points of `A` after restriction of scalars.

## References

This supports the "Base change. `K ⊗[k] A` as a Hopf algebra over `K`" item in Layer 0 of the
Tau Ceti reductive-groups roadmap.  The underlying tensor-product Hopf algebra instance is due to
Amelia Livingston and Andrew Yang in Mathlib.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The scalar extension of an `R`-algebra `A` along `R → S`.  When `A` is a Hopf algebra over
`R`, Mathlib's tensor-product Hopf algebra instance equips this algebra with a Hopf algebra
structure over `S`. -/
abbrev BaseChange [Semiring A] [Algebra R A] :=
  S ⊗[R] A

namespace BaseChange

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The canonical inclusion of an algebra into its scalar extension. -/
def inclusion [Semiring A] [Algebra R A] : A →ₐ[R] HopfAlgebra.BaseChange R S A :=
  Algebra.TensorProduct.includeRight

@[simp]
theorem inclusion_apply [Semiring A] [Algebra R A] (a : A) :
    inclusion (R := R) (S := S) a = 1 ⊗ₜ[R] a :=
  Algebra.TensorProduct.includeRight_apply a

/-- The antipode on the scalar extension acts on pure tensors by applying the antipodes in
each tensor factor. -/
@[simp]
theorem antipode_tmul [Semiring A] [HopfAlgebra R A] (s : S) (a : A) :
    HopfAlgebra.antipode S (s ⊗ₜ[R] a : HopfAlgebra.BaseChange R S A) =
      HopfAlgebra.antipode S s ⊗ₜ[R] HopfAlgebra.antipode R a :=
  by
    rw [TensorProduct.antipode_def]
    rfl

/-- The counit on the scalar extension evaluates a pure tensor by applying the original counit
to the algebra factor and using the result as a scalar on the base-changed coefficient. -/
@[simp]
theorem counit_tmul [Semiring A] [Algebra R A] [Coalgebra R A] (s : S) (a : A) :
    Coalgebra.counit (R := S) (s ⊗ₜ[R] a : HopfAlgebra.BaseChange R S A) =
      Coalgebra.counit (R := R) a • s :=
  TensorProduct.counit_tmul s a

/-- The comultiplication on the scalar extension is the tensor-product comultiplication,
reassociated by `tensorTensorTensorComm`. -/
@[simp]
theorem comul_tmul [Semiring A] [Algebra R A] [Coalgebra R A] (s : S) (a : A) :
    Coalgebra.comul (R := S) (s ⊗ₜ[R] a : HopfAlgebra.BaseChange R S A) =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A
        (Coalgebra.comul (R := S) s ⊗ₜ[R] Coalgebra.comul (R := R) a) :=
  TensorProduct.comul_tmul s a

end BaseChange

end HopfAlgebra

namespace AlgHom

variable {R S A B C : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

/-- Algebra-valued points of a base-changed algebra are the same as algebra-valued points of the
original algebra after restriction of scalars. -/
def baseChangeValueEquiv : (A →ₐ[R] B) ≃ (HopfAlgebra.BaseChange R S A →ₐ[S] B) :=
  _root_.AlgHom.liftEquiv R S A B

/-- Extend an `R`-algebra-valued point of `A` to an `S`-algebra-valued point of the base change. -/
def baseChangeValue (f : A →ₐ[R] B) : HopfAlgebra.BaseChange R S A →ₐ[S] B :=
  baseChangeValueEquiv (R := R) (S := S) f

/-- The base-changed value of an algebra point sends a pure tensor to scalar multiplication by
the coefficient followed by the original point. -/
@[simp]
theorem baseChangeValue_tmul (f : A →ₐ[R] B) (s : S) (a : A) :
    baseChangeValue (R := R) (S := S) f (s ⊗ₜ[R] a) = s • f a :=
  _root_.AlgHom.liftEquiv_tmul f s a

/-- Restricting a base-changed point along the canonical inclusion recovers the original point. -/
@[simp]
theorem baseChangeValue_include (f : A →ₐ[R] B) (a : A) :
    baseChangeValue (R := R) (S := S) f
        (HopfAlgebra.BaseChange.inclusion (S := S) a) = f a := by
  simp [HopfAlgebra.BaseChange.inclusion]

/-- Evaluating the inverse points equivalence is restriction along the canonical inclusion into
the scalar extension. -/
@[simp]
theorem baseChangeValueEquiv_symm_apply (f : HopfAlgebra.BaseChange R S A →ₐ[S] B) (a : A) :
    (baseChangeValueEquiv (R := R) (S := S)).symm f a =
      f (HopfAlgebra.BaseChange.inclusion (S := S) a) :=
  by
    change ((AlgHom.liftEquiv R S A B).symm f) a = f (1 ⊗ₜ[R] a)
    exact _root_.AlgHom.liftEquiv_symm_apply f a

variable [Semiring C] [Algebra S C] [Algebra R C] [IsScalarTower R S C]

/-- Base-changed values are natural in the target algebra under postcomposition. -/
@[simp]
theorem comp_baseChangeValue (g : B →ₐ[S] C) (f : A →ₐ[R] B) :
    g.comp (baseChangeValue (R := R) (S := S) f) =
      baseChangeValue (R := R) (S := S) ((g.restrictScalars R).comp f) := by
  ext a
  simp

/-- The inverse points equivalence is natural in the target algebra under postcomposition. -/
@[simp]
theorem baseChangeValueEquiv_symm_comp (g : B →ₐ[S] C)
    (f : HopfAlgebra.BaseChange R S A →ₐ[S] B) :
    (baseChangeValueEquiv (R := R) (S := S)).symm (g.comp f) =
      (g.restrictScalars R).comp ((baseChangeValueEquiv (R := R) (S := S)).symm f) := by
  ext a
  simp [baseChangeValueEquiv]

end AlgHom

end TauCeti
