/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Coefficient algebra maps between convolution algebras

Precomposition by a coalgebra homomorphism is linear over the coefficient algebra,
not just over the base ring. In particular, transposing bialgebra multiplication
is a homomorphism of convolution algebras over the coefficients.
Tensoring with either counit gives two more such homomorphisms, the exterior products
with the convolution unit; by `WithConv.mulTensor_convMul` and `WithConv.mulTensor_one_one`
their products recover the exterior product of arbitrary linear maps.

## References

These constructions use Mathlib's `CoalgHom.convPrecomp` and Tau Ceti's
`WithConv.mulTensor` and `WithConv.mulTensor_convMul`.
-/

public noncomputable section

open TensorProduct WithConv

namespace CoalgHom

variable {R C M N : Type*} [CommSemiring R] [CommSemiring C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [Coalgebra R M]
  [AddCommMonoid N] [Module R N] [Coalgebra R N]

/-- Precomposition as an algebra homomorphism over the coefficient algebra. -/
def convPrecompCoefficients (h : N →ₗc[R] M) :
    WithConv (M →ₗ[R] C) →ₐ[C] WithConv (N →ₗ[R] C) where
  __ := (h.convPrecomp (A := C)).toRingHom
  commutes' c := by ext n; simp

/-- Precomposition evaluates by composing the underlying linear maps. -/
@[simp]
theorem convPrecompCoefficients_apply (h : N →ₗc[R] M) (f : WithConv (M →ₗ[R] C)) :
    (h.convPrecompCoefficients f).ofConv = f.ofConv.comp h.toLinearMap := (rfl)

end CoalgHom

namespace WithConv

variable {R C M N : Type*} [CommSemiring R] [CommSemiring C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [Coalgebra R M]
  [AddCommMonoid N] [Module R N] [Coalgebra R N]

/-- Tensoring a convolution-algebra element with the counit on the right. -/
def tensorCounitRight (R C M N : Type*) [CommSemiring R] [CommSemiring C] [Algebra R C]
    [AddCommMonoid M] [Module R M] [Coalgebra R M]
    [AddCommMonoid N] [Module R N] [Coalgebra R N] :
    WithConv (M →ₗ[R] C) →ₐ[C] WithConv (M ⊗[R] N →ₗ[R] C) :=
  CoalgHom.convPrecompCoefficients ((Coalgebra.TensorProduct.rid R R M).toCoalgHom.comp
    (Coalgebra.TensorProduct.map (CoalgHom.id R M) (Coalgebra.counitCoalgHom R N)))

/-- Tensoring a convolution-algebra element with the counit on the left. -/
def tensorCounitLeft (R C M N : Type*) [CommSemiring R] [CommSemiring C] [Algebra R C]
    [AddCommMonoid M] [Module R M] [Coalgebra R M]
    [AddCommMonoid N] [Module R N] [Coalgebra R N] :
    WithConv (N →ₗ[R] C) →ₐ[C] WithConv (M ⊗[R] N →ₗ[R] C) :=
  CoalgHom.convPrecompCoefficients ((Coalgebra.TensorProduct.lid R N).toCoalgHom.comp
    (Coalgebra.TensorProduct.map (Coalgebra.counitCoalgHom R M) (CoalgHom.id R N)))

/-- The right-counit map is the exterior product with the convolution unit. -/
@[simp]
theorem tensorCounitRight_apply (f : WithConv (M →ₗ[R] C)) :
    tensorCounitRight R C M N f = mulTensor f 1 := by
  apply ofConv_injective
  apply TensorProduct.ext
  ext m n
  simp [tensorCounitRight, Algebra.smul_def, mul_comm]

/-- The left-counit map is the exterior product with the convolution unit. -/
@[simp]
theorem tensorCounitLeft_apply (f : WithConv (N →ₗ[R] C)) :
    tensorCounitLeft R C M N f = mulTensor 1 f := by
  apply ofConv_injective
  apply TensorProduct.ext
  ext m n
  simp [tensorCounitLeft, Algebra.smul_def]

end WithConv

namespace TauCeti
namespace Bialgebra

variable (R C A : Type*) [CommSemiring R] [CommSemiring C] [Algebra R C]
  [Semiring A] [_root_.Bialgebra R A]

/-- Transposing multiplication is a homomorphism of convolution algebras over the coefficients. -/
def convolutionDelta : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  (_root_.Bialgebra.mulCoalgHom R A).convPrecompCoefficients

/-- Transposed multiplication is precomposition by the multiplication coalgebra map. -/
theorem convolutionDelta_def :
    convolutionDelta R C A = (_root_.Bialgebra.mulCoalgHom R A).convPrecompCoefficients := (rfl)

/-- The transposed multiplication evaluates at the product on a pure tensor. -/
@[simp]
theorem convolutionDelta_apply_tmul (f : WithConv (A →ₗ[R] C)) (a b : A) :
    (convolutionDelta R C A f).ofConv (a ⊗ₜ[R] b) = f.ofConv (a * b) := by
  simp [convolutionDelta]

end Bialgebra
end TauCeti
