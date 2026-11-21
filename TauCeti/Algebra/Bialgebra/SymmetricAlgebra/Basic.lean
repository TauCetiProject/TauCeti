/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra

/-!
# Convolution on the symmetric bialgebra

Mathlib equips `SymmetricAlgebra R M` with the cocommutative bialgebra structure in which each
generator `ι x` is primitive, `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x`. Consequently the convolution product
of two `R`-algebra maps out of `SymmetricAlgebra R M` adds their values on generators.

## Main declarations

* `SymmetricAlgebra.convMul_apply_ι`: convolution of algebra maps evaluates on generators by
  adding their values.

## References

The bialgebra structure on the symmetric algebra is Robert Hawkins' Mathlib work in
`Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`; the convolution product on algebra maps out of a
bialgebra is `Mathlib.RingTheory.Bialgebra.Convolution`.
-/

public section

namespace SymmetricAlgebra

/-- The convolution product of two points of a symmetric algebra is, on each generator, the sum
of their values: `(F * G)(ι x) = F(ι x) + G(ι x)`. -/
@[simp]
theorem convMul_apply_ι {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] (F G : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    (F * G).ofConv (ι R M x) = F.ofConv (ι R M x) + G.ofConv (ι R M x) := by
  simpa [Algebra.TensorProduct.lift_tmul] using AlgHom.convMul_apply F G (ι R M x)

end SymmetricAlgebra
