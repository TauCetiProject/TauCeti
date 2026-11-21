/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change along a ring epimorphism, and rational vector spaces

If `R → S` is an epimorphism of commutative rings (`Algebra.IsEpi R S`), then an `S`-module is
already its own extension of scalars from `R` to `S`: the identity, viewed as `R`-linear, exhibits
it as such a base change. The main instance is `ℤ → ℚ`: any additive map out of a `ℚ`-vector space
into a `ℚ`-module is automatically `ℚ`-linear. Consequently, for a `ℚ`-algebra `A`, the concrete
tensor product `A ⊗[ℚ] U` is a base change of `U` along `ℤ → A`, not merely along `ℚ → A`.

This is what allows a `ℚ`-vector space to be fed to constructions that take an integral module
together with an abstract model of its complexification, such as the conjugation and the pure
Hodge structures of `TauCeti/Geometry/Hodge/`.

## Main results

* `TauCeti.isBaseChange_restrictScalars_id`: for an epimorphism `R → S`, the identity of an
  `S`-module, viewed as `R`-linear, exhibits it as its own base change along `R → S`.
* `TauCeti.isBaseChange_ratTensorMap`: for a `ℚ`-algebra `A`, the map `u ↦ 1 ⊗ₜ u` exhibits
  `A ⊗[ℚ] U` as the base change of `U` along `ℤ → A`.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-- If `R → S` is an epimorphism of commutative rings, then every `S`-module `U` is its own base
change along `R → S`: the identity map, viewed as a map of `R`-modules, exhibits `U` as the
extension of scalars of `U` from `R` to `S`. For `ℤ → ℚ`, this says that a `ℚ`-vector space is its
own rationalification. -/
theorem isBaseChange_restrictScalars_id (R S U : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Algebra.IsEpi R S] [AddCommMonoid U] [Module R U] [Module S U]
    [IsScalarTower R S U] :
    IsBaseChange S ((LinearMap.id : U →ₗ[S] U).restrictScalars R) :=
  .of_equiv (TensorProduct.lid' R S U) fun _ ↦ by simp

variable (A : Type*) [CommRing A] [Algebra ℚ A]
variable (U : Type*) [AddCommGroup U] [Module ℚ U]

/-- The canonical map of a rational vector space into its scalar extension `A ⊗[ℚ] U`, viewed as
a map of `ℤ`-modules. -/
def ratTensorMap : U →ₗ[ℤ] A ⊗[ℚ] U :=
  (TensorProduct.mk ℚ A U 1).restrictScalars ℤ

@[simp]
theorem ratTensorMap_apply (u : U) : ratTensorMap A U u = 1 ⊗ₜ[ℚ] u := (rfl)

/-- For a `ℚ`-algebra `A`, the tensor product `A ⊗[ℚ] U` of a rational vector space is a base
change of `U` along `ℤ → A`, and not only along `ℚ → A`. -/
theorem isBaseChange_ratTensorMap : IsBaseChange A (ratTensorMap A U) := by
  have := (isBaseChange_restrictScalars_id ℤ ℚ U).comp (TensorProduct.isBaseChange ℚ U A)
  rwa [LinearMap.restrictScalars_id, LinearMap.comp_id] at this

end TauCeti
