/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The exponential specialization of a monoid algebra

The functional equation `e^{aX} e^{bX} = e^{(a+b)X}` of the exponential power series
(`PowerSeries.exp_mul_exp_eq_exp_add`) says that `a ↦ e^{aX}` is a homomorphism from the additive
group of a `ℚ`-algebra `R` to the multiplicative monoid of `R⟦X⟧`. Composed with an additive map
`φ : M →+ R` and extended linearly, it turns the monoid algebra `k[M]` into power series:

`∑ c_m e^m ↦ ∑ c_m e^{φ(m) X}`.

This is the **exponential specialization** of `k[M]` along `φ`. It is the device by which a
formal identity in a group algebra, such as the Weyl character formula, is turned into a
numerical identity between its coefficients: the constant coefficient of the image is the sum of
the coefficients (the augmentation), and the higher coefficients are the moments
`∑ c_m φ(m)^n / n!`.

## Main definitions

* `PowerSeries.expMonoidHom`: `a ↦ e^{aX}` as a monoid homomorphism `Multiplicative R →* R⟦X⟧`.
* `AddMonoidAlgebra.expAlgHom φ`: the exponential specialization `k[M] →ₐ[k] R⟦X⟧` along an
  additive map `φ : M →+ R`.

## Main results

* `PowerSeries.constantCoeff_rescale`: rescaling the variable keeps the constant coefficient.
* `AddMonoidAlgebra.expAlgHom_single`: `e^m ↦ e^{φ(m) X}`.
* `AddMonoidAlgebra.constantCoeff_expAlgHom`: the constant coefficient of the exponential
  specialization is the sum of the coefficients.
-/

public section

namespace PowerSeries

/-- Rescaling the variable does not change the constant coefficient. -/
@[simp]
theorem constantCoeff_rescale {R : Type*} [CommSemiring R] (a : R) (f : R⟦X⟧) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- **The exponential `a ↦ e^{aX}` as a monoid homomorphism** `Multiplicative R →* R⟦X⟧`. That
this is a homomorphism is the functional equation `PowerSeries.exp_mul_exp_eq_exp_add`. -/
noncomputable def expMonoidHom : Multiplicative R →* R⟦X⟧ where
  toFun a := rescale a.toAdd (exp R)
  map_one' := by simp
  map_mul' a b := by simp [exp_mul_exp_eq_exp_add]

variable {R}

private theorem expMonoidHom_apply_def (a : Multiplicative R) :
    expMonoidHom R a = rescale a.toAdd (exp R) :=
  rfl

/-- The exponential monoid homomorphism sends `a` to the exponential series rescaled by `a`. -/
@[simp]
theorem expMonoidHom_apply (a : Multiplicative R) :
    expMonoidHom R a = rescale a.toAdd (exp R) :=
  expMonoidHom_apply_def a

/-- `e^{aX}` is the exponential series rescaled by `a`. -/
theorem expMonoidHom_ofAdd (a : R) :
    expMonoidHom R (Multiplicative.ofAdd a) = rescale a (exp R) := by
  simp only [expMonoidHom_apply, toAdd_ofAdd]

end PowerSeries

namespace AddMonoidAlgebra

open PowerSeries

variable {k : Type*} [CommSemiring k] {M : Type*} [AddMonoid M] {R : Type*} [CommRing R]
  [Algebra ℚ R] [Algebra k R]

/-- **The exponential specialization** of the monoid algebra `k[M]` along an additive map
`φ : M →+ R`: the `k`-algebra homomorphism `k[M] →ₐ[k] R⟦X⟧` sending `e^m` to `e^{φ(m) X}`. Its
constant coefficient is the augmentation `∑ c_m e^m ↦ ∑ c_m`
(`AddMonoidAlgebra.constantCoeff_expAlgHom`), and its higher coefficients are the moments of the
coefficients against `φ`. -/
noncomputable def expAlgHom (φ : M →+ R) : k[M] →ₐ[k] R⟦X⟧ :=
  lift k R⟦X⟧ M ((expMonoidHom R).comp (AddMonoidHom.toMultiplicative φ))

/-- The exponential specialization sends `c e^m` to `c e^{φ(m) X}`, the scalar `c` acting through
`algebraMap k R⟦X⟧`.

The scalar is written as a ring element rather than as `c • _`: for `k = ℤ` the scalar action of
`ℤ` on `R⟦X⟧` through the algebra structure is not syntactically the action `n • p` elaborates
to, whereas `algebraMap ℤ R⟦X⟧ n` simplifies to the cast `(n : R⟦X⟧)`. -/
@[simp]
theorem expAlgHom_single (φ : M →+ R) (m : M) (c : k) :
    expAlgHom φ (single m c) = algebraMap k R⟦X⟧ c * rescale (φ m) (exp R) := by
  rw [expAlgHom, lift_single, Algebra.smul_def, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, expMonoidHom_ofAdd]

/-- **The constant coefficient of the exponential specialization is the sum of the
coefficients**: the specialization at `X = 0` is the augmentation of the monoid algebra. -/
@[simp]
theorem constantCoeff_expAlgHom (φ : M →+ R) (f : k[M]) :
    constantCoeff (expAlgHom φ f) = algebraMap k R (f.coeff.sum fun _ c ↦ c) := by
  rw [expAlgHom, lift_apply, map_finsuppSum, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp [Algebra.algebraMap_eq_smul_one]

end AddMonoidAlgebra
