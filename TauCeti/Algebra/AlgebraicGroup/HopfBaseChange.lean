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
are described on pure tensors, the canonical inclusion `A →ₐ[R] S ⊗[R] A` is named, and
`AlgHom.baseChangeValue` packages the standard tensor-product adjunction for points.

## Main declarations

* `HopfAlgebra.BaseChange`: the scalar extension `S ⊗[R] A` of an `R`-Hopf algebra.
* `HopfAlgebra.baseChangeIncludeRight`: the canonical map `A →ₐ[R] S ⊗[R] A`.
* `AlgHom.baseChangeValue`: algebra maps out of the scalar extension are equivalent to
  algebra maps out of the original algebra into the restricted target.

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
variable [Semiring A] [_root_.HopfAlgebra R A]

/-- The scalar extension of an `R`-Hopf algebra `A` along `R → S`, equipped with Mathlib's
tensor-product Hopf algebra structure over `S`. -/
abbrev BaseChange :=
  S ⊗[R] A

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

/-- The canonical algebra map from a Hopf algebra to its scalar extension. -/
def baseChangeIncludeRight : A →ₐ[R] BaseChange R S A :=
  Algebra.TensorProduct.includeRight

/-- The canonical map into the scalar extension sends `a` to `1 ⊗ a`. -/
@[simp]
lemma baseChangeIncludeRight_apply (a : A) :
    baseChangeIncludeRight R S A a = (1 : S) ⊗ₜ[R] a := by
  rfl

/-- The scalar-extended counit after the canonical inclusion is the original counit followed by
the base map. -/
@[simp]
lemma baseChange_counit_includeRight (a : A) :
    counit (R := S) (A := BaseChange R S A) (baseChangeIncludeRight R S A a) =
      algebraMap R S (counit (R := R) a) := by
  simp [Algebra.smul_def]

/-- The scalar-extended antipode after the canonical inclusion is the canonical inclusion after
the original antipode. -/
@[simp]
lemma baseChange_antipode_includeRight (a : A) :
    _root_.HopfAlgebraStruct.antipode S (A := BaseChange R S A)
        (baseChangeIncludeRight R S A a) =
      baseChangeIncludeRight R S A (_root_.HopfAlgebraStruct.antipode R a) := by
  simp

end HopfAlgebra

namespace AlgHom

variable {R S A B C : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A]
variable [CommSemiring B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

/-- Algebra maps from a scalar extension are the same as algebra maps from the original algebra
into the restricted target.  For a Hopf algebra `A`, this identifies `S`-valued points of
`S ⊗[R] A` with `R`-algebra maps `A → B`, where `B` is regarded as an `R`-algebra by restriction
of scalars. -/
noncomputable abbrev baseChangeValue : (A →ₐ[R] B) ≃ (S ⊗[R] A →ₐ[S] B) :=
  AlgHom.liftEquiv R S A B

/-- The base-change adjunction sends `f : A →ₐ[R] B` to its `S`-linear extension, so on pure
tensors it is given by `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangeValue_apply (f : A →ₐ[R] B) (s : S) (a : A) :
    baseChangeValue (R := R) (S := S) (A := A) (B := B) f (s ⊗ₜ[R] a) = s • f a := by
  rfl

/-- The inverse of the base-change adjunction restricts an `S`-algebra map along `a ↦ 1 ⊗ a`. -/
@[simp]
lemma baseChangeValue_symm_apply (f : S ⊗[R] A →ₐ[S] B) (a : A) :
    (baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm f a = f (1 ⊗ₜ[R] a) := by
  rfl

/-- The inverse of `baseChangeValue` is precomposition with the canonical inclusion, after
restricting scalars on the target. -/
lemma baseChangeValue_symm_comp (f : S ⊗[R] A →ₐ[S] B) :
    (baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm f =
      (f.restrictScalars R).comp Algebra.TensorProduct.includeRight := by
  rfl

/-- Two maps from the scalar extension are equal if they agree after precomposition with
`a ↦ 1 ⊗ a`. -/
lemma baseChangeValue_ext {f g : S ⊗[R] A →ₐ[S] B}
    (h : (baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm f =
      (baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm g) :
    f = g :=
  (baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm.injective h

variable [CommSemiring C] [Algebra S C] [Algebra R C] [IsScalarTower R S C]

/-- `baseChangeValue` is natural in the target algebra. -/
lemma baseChangeValue_comp (φ : B →ₐ[S] C) (f : A →ₐ[R] B) :
    baseChangeValue (R := R) (S := S) (A := A) (B := C)
        ((φ.restrictScalars R).comp f) =
      φ.comp (baseChangeValue (R := R) (S := S) (A := A) (B := B) f) := by
  apply Algebra.TensorProduct.ext_ring
  ext a
  simp

/-- The inverse of `baseChangeValue` is natural in the target algebra. -/
lemma baseChangeValue_symm_comp_target (φ : B →ₐ[S] C) (f : S ⊗[R] A →ₐ[S] B) :
    (baseChangeValue (R := R) (S := S) (A := A) (B := C)).symm (φ.comp f) =
      (φ.restrictScalars R).comp
        ((baseChangeValue (R := R) (S := S) (A := A) (B := B)).symm f) := by
  ext a
  rfl

end AlgHom

end TauCeti
