/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Domain
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Tensor squares and base change of a subalgebra over a subring

Let `H` be an algebra over `K`, and `A` an `R`-subalgebra of `H` for an `R`-algebra `K`. This file
compares `A` with `H` when `K` is the fraction field of `R`.

## Main declarations

* `Subalgebra.tensorSquareMap`: the canonical map `A ⊗[R] A → H ⊗[K] H`, the `Subalgebra`
  analogue of `Subring.tensorSquareMap`.
* `Subalgebra.tensorSquareMap_injective`: it is injective when `A` is flat over the domain `R`
  and `K` is the fraction field of `R`.
* `Subalgebra.isBaseChange_val`: when `A` spans `H` over the fraction field `K` of `R`, the
  inclusion `A → H` is the base change of `A` to `K`.
-/

public section

open scoped TensorProduct

namespace Subalgebra

section Semiring

variable {R K H : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K] [Semiring H]
  [Algebra K H] [Algebra R H] [IsScalarTower R K H]

variable (K) in
/-- The canonical map from the tensor square over `R` of an `R`-subalgebra `A` of a `K`-algebra
`H` to the tensor square of `H` over `K`. On pure tensors it applies the inclusion of `A` in both
factors. -/
noncomputable def tensorSquareMap (A : Subalgebra R H) : A ⊗[R] A →ₐ[R] H ⊗[K] H :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H).restrictScalars R |>.comp A.val)
    ((Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H).restrictScalars R |>.comp A.val)
    fun x y ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
      exact (Commute.one_right _).tmul (Commute.one_left _)

/-- The canonical map `A ⊗[R] A → H ⊗[K] H` sends `x ⊗ y` to `x ⊗ y`. -/
@[simp]
theorem tensorSquareMap_tmul (A : Subalgebra R H) (x y : A) :
    tensorSquareMap K A (x ⊗ₜ y) = (x : H) ⊗ₜ[K] (y : H) := by
  rw [tensorSquareMap, Algebra.TensorProduct.lift_tmul]
  simp

/-- An `R`-subalgebra `A` of an algebra `H` over the fraction field `K` of `R` which spans `H`
over `K` has `H` as its localization at the nonzero elements of `R`: the inclusion `A → H` is the
base change of `A` to `K`. -/
theorem isBaseChange_val [IsFractionRing R K] (A : Subalgebra R H)
    (hspan : Submodule.span K (A : Set H) = ⊤) :
    IsBaseChange K (A.val.toLinearMap : A →ₗ[R] H) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mp
    (A.toSubmodule.isLocalizedModule_subtype_of_span_eq_top (nonZeroDivisors R) hspan)

end Semiring

variable {R K H : Type*} [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [Ring H]
  [Algebra K H] [Algebra R H] [IsScalarTower R K H]

/-- For a flat `R`-subalgebra `A` of an algebra over the fraction field `K` of the domain `R`, the
canonical map `A ⊗[R] A → H ⊗[K] H` is injective. -/
-- Composed with the isomorphism `H ⊗[K] H ≅ H ⊗[R] H` of a localization, it is the tensor square
-- of the inclusion of `A`, which is injective since `A` is flat over the domain `R`.
theorem tensorSquareMap_injective [IsFractionRing R K] (A : Subalgebra R H)
    [Module.Flat R A] : Function.Injective (tensorSquareMap K A) := by
  have : TensorProduct.CompatibleSMul R K H H :=
    IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors R) K H H
  have hcomp : (TensorProduct.mapOfCompatibleSMul R K R H H : H ⊗[K] H →ₗ[R] H ⊗[R] H) ∘ₗ
      (tensorSquareMap K A).toLinearMap =
        TensorProduct.map A.val.toLinearMap A.val.toLinearMap :=
    TensorProduct.ext' fun x y ↦ by simp
  refine .of_comp (f := TensorProduct.mapOfCompatibleSMul R K R H H) ?_
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.coe_comp, hcomp]
  exact TensorProduct.map_injective_of_flat_flat_of_isDomain _ _
    Subtype.val_injective Subtype.val_injective

end Subalgebra
