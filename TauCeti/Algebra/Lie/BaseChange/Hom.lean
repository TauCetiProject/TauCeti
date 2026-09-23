/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Extension of scalars of a homomorphism of Lie algebras

Mathlib extends the scalars of a Lie algebra `L` over `R` to `A ⊗[R] L` over an `R`-algebra `A`,
and `LieAlgebra.ExtendScalars.map` extends a homomorphism along a map of coefficient algebras.
That map is a homomorphism of Lie algebras over `R`, which is the right generality when the
coefficients move.  When the coefficients stay put -- the case a descent argument needs -- the
same underlying linear map `LinearMap.baseChange` is `A`-linear, and the resulting `A`-Lie
homomorphism `LieHom.baseChange` is what this file records.

The point of the `A`-linear form is that its kernel is a `LieIdeal A (A ⊗[R] L)`, so it can be
compared with `LieSubmodule.baseChange`.  The comparison is an equality over a flat coefficient
algebra, and also for a surjective homomorphism over an arbitrary one; both readings are inherited
from `LinearMap.ker_baseChange` and `LinearMap.ker_baseChange_of_surjective`.  Surjectivity itself
is right-exactness of the tensor product and asks nothing of `A`.

## Main definitions

* `LieHom.baseChange`: the extension of scalars `A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L'` of a homomorphism of
  Lie algebras.

## Main results

* `LieHom.baseChange_surjective`: extension of scalars preserves surjectivity.
* `LieHom.ker_baseChange` and `LieHom.ker_baseChange_of_surjective`: **the kernel of an extended
  homomorphism is the extension of its kernel**, over a flat coefficient algebra, respectively for
  a surjective homomorphism over an arbitrary one.
-/

public section

open TensorProduct

namespace LieHom

universe u v w x

variable {R : Type u} {L : Type w} {L' : Type x}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (A : Type v) [CommRing A] [Algebra R A] (f : L →ₗ⁅R⁆ L')

/-- **The extension of scalars of a homomorphism of Lie algebras**, as a homomorphism of Lie
algebras over the extended coefficients.

Its underlying map is `LinearMap.baseChange`, so it agrees with
`LieAlgebra.ExtendScalars.map (AlgHom.id R A) f`; the difference is that this form is linear over
`A` rather than over `R`, which is what makes its kernel an ideal of `A ⊗[R] L` over `A`. -/
def baseChange : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L' where
  __ := LinearMap.baseChange A (f : L →ₗ[R] L')
  map_lie' {x y} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
        simp [LieAlgebra.ExtendScalars.bracket_tmul]
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_lie, map_add, hx, hz]

@[simp]
theorem coe_baseChange :
    ((baseChange A f : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L') : A ⊗[R] L →ₗ[A] A ⊗[R] L') =
      LinearMap.baseChange A (f : L →ₗ[R] L') :=
  (rfl)

theorem baseChange_apply (x : A ⊗[R] L) :
    baseChange A f x = LinearMap.baseChange A (f : L →ₗ[R] L') x :=
  (rfl)

@[simp]
theorem baseChange_tmul (a : A) (x : L) : baseChange A f (a ⊗ₜ[R] x) = a ⊗ₜ[R] f x := by
  rw [baseChange_apply, LinearMap.baseChange_tmul, coe_toLinearMap]

/-- Extension of scalars preserves surjectivity: the tensor product is right exact. -/
theorem baseChange_surjective (hf : Function.Surjective f) :
    Function.Surjective (baseChange A f) :=
  LinearMap.baseChange_surjective A hf

/-- **Over a flat coefficient algebra, extension of scalars commutes with kernels.**  The kernel
of the extended homomorphism is the extension of the kernel, because tensoring with a flat module
carries the exact pair `ker f ↪ L → L'` to an exact pair. -/
theorem ker_baseChange [Module.Flat R A] : (baseChange A f).ker = f.ker.baseChange A := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.coe_baseChange, ker_toSubmodule,
    ker_toSubmodule, coe_baseChange]
  exact LinearMap.ker_baseChange A (f : L →ₗ[R] L')

/-- **For a surjective homomorphism, extension of scalars commutes with kernels over an arbitrary
coefficient algebra.**  Right-exactness of the tensor product replaces flatness here. -/
theorem ker_baseChange_of_surjective (hf : Function.Surjective f) :
    (baseChange A f).ker = f.ker.baseChange A := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.coe_baseChange, ker_toSubmodule,
    ker_toSubmodule, coe_baseChange]
  exact LinearMap.ker_baseChange_of_surjective A (f : L →ₗ[R] L') hf

end LieHom
