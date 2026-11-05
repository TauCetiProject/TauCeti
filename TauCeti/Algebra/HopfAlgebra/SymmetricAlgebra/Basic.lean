/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf structure on a symmetric algebra

Mathlib equips `SymmetricAlgebra R M` with the cocommutative bialgebra structure in which each
generator `ι x` is primitive, `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and `ε(ι x) = 0`, but it stops short
of the antipode. Over a commutative ring `R` the symmetric algebra is a *Hopf* algebra: the
antipode is the algebra map sending each `ι x` to `-ι x`.

## Main declarations

* `SymmetricAlgebra.instHopfAlgebra`: the Hopf algebra structure on `SymmetricAlgebra R M` over
  a commutative ring `R`.
* `SymmetricAlgebra.antipode_ι`: the Hopf antipode sends each generator to its negative.
* `SymmetricAlgebra.convMul_apply_ι`: convolution of algebra maps evaluates on generators by
  adding their values.

## References

The cocommutative bialgebra structure on the symmetric algebra is Robert Hawkins' Mathlib work
in `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`. The Hopf-algebra-from-an-antipode
constructor `HopfAlgebra.ofAlgHom` is from `Mathlib.RingTheory.HopfAlgebra.Basic`.
-/

public section

open HopfAlgebra

namespace SymmetricAlgebra

section Hopf

variable (R M : Type*) [CommRing R] [AddCommMonoid M] [Module R M]

/-- The antipode of the symmetric-algebra Hopf algebra: the `R`-algebra map sending each
generator `ι x` to `-ι x`. -/
noncomputable def antipodeHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  lift (-ι R M)

/-- The algebra map `antipodeHom` sends each generator `ι x` to `-ι x`. -/
@[simp]
theorem antipodeHom_ι (x : M) : antipodeHom R M (ι R M x) = -ι R M x := by
  simp [antipodeHom]

/-- The symmetric algebra over a commutative ring is a Hopf algebra: its antipode sends each
generator `ι x` to `-ι x`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (antipodeHom R M)
    -- `lift_tmul` does not fire here: the commutativity proof in this hypothesis of
    -- `HopfAlgebra.ofAlgHom` has a type that matches `lift_tmul` only up to unfolding
    -- `AlgHom.id`, so we unfold `Algebra.TensorProduct.lift` instead.
    (by ext x; simp [Algebra.TensorProduct.lift, algebraMapInv_ι])
    (by ext x; simp [algebraMapInv_ι])

/-- The Hopf-algebra antipode on a symmetric algebra sends each generator `ι x` to `-ι x`. -/
@[simp]
theorem antipode_ι (x : M) : antipode R (ι R M x) = -ι R M x :=
  antipodeHom_ι R M x

end Hopf

/-- The convolution product of two points of a symmetric algebra is, on each generator, the sum
of their values: `(F * G)(ι x) = F(ι x) + G(ι x)`. -/
@[simp]
theorem convMul_apply_ι {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] (F G : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    (F * G).ofConv (ι R M x) = F.ofConv (ι R M x) + G.ofConv (ι R M x) := by
  simpa [Algebra.TensorProduct.lift_tmul] using AlgHom.convMul_apply F G (ι R M x)

end SymmetricAlgebra
