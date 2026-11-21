/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Complements on power series

Mathlib's `PowerSeries.constantCoeff` is the constant coefficient `S⟦X⟧ → S` as a ring
homomorphism. This file records it as a homomorphism of `A`-algebras for any commutative semiring
`A` over which `S` is an algebra (evaluation at `X = 0`), as well as basic `@[simp]` lemmas on
univariate formal power series missing from `Mathlib.RingTheory.PowerSeries.Basic`.

## Main definitions

* `PowerSeries.constantCoeffAlgHom A`: the constant coefficient `S⟦X⟧ →ₐ[A] S`.

## Main results

* `PowerSeries.constantCoeffAlgHom_comp_toAlgHom`: evaluation at `X = 0` is a retraction of the
  inclusion of constants.
* `PowerSeries.constantCoeff_map`: the constant coefficient of `PowerSeries.map f p` is
  `f (constantCoeff p)`.
-/

public section

open scoped PowerSeries

namespace PowerSeries

section ConstantCoeff

variable (A : Type*) {S : Type*} [CommSemiring A] [Semiring S] [Algebra A S]

/-- The constant coefficient `S⟦X⟧ → S`, that is, evaluation at `X = 0`, as a homomorphism of
`A`-algebras. -/
noncomputable def constantCoeffAlgHom : S⟦X⟧ →ₐ[A] S where
  toRingHom := constantCoeff
  commutes' a := by rw [RingHom.toFun_eq_coe, algebraMap_apply, constantCoeff_C]

variable {A}

@[simp]
theorem constantCoeffAlgHom_apply (f : S⟦X⟧) : constantCoeffAlgHom A f = constantCoeff f := (rfl)

/-- As a ring homomorphism, `PowerSeries.constantCoeffAlgHom` is `PowerSeries.constantCoeff`. -/
@[simp]
theorem constantCoeffAlgHom_toRingHom :
    (constantCoeffAlgHom A (S := S) : S⟦X⟧ →+* S) = constantCoeff :=
  (rfl)

/-- Evaluation at `X = 0` is a retraction of the inclusion of constants. -/
@[simp]
theorem constantCoeffAlgHom_comp_toAlgHom {S : Type*} [CommSemiring S] [Algebra A S] :
    (constantCoeffAlgHom A).comp (IsScalarTower.toAlgHom A S S⟦X⟧) = AlgHom.id A S :=
  AlgHom.ext fun s ↦ by simp

end ConstantCoeff

section Map

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The constant coefficient of `PowerSeries.map f p` is `f (constantCoeff p)`. -/
@[simp]
theorem constantCoeff_map (f : R →+* S) (p : R⟦X⟧) :
    constantCoeff (map f p) = f (constantCoeff p) :=
  MvPowerSeries.constantCoeff_map f p

end Map

end PowerSeries
