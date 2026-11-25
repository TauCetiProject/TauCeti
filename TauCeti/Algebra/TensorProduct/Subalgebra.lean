/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.RingTheory.TensorProduct.AlgEquiv
import Mathlib.RingTheory.Flat.Domain
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Tensor squares and base change of a subalgebra over a subring

Let `H` be an algebra over `K`, and `A` an `R`-subalgebra of `H` for an `R`-algebra `K`. This file
compares `A` with `H` when `K` is a localization of `R`, for instance the fraction field of a
domain `R`.

## Main declarations

* `Subalgebra.tensorSquareMap`: the canonical map `A ⊗[R] A → H ⊗[K] H`, the `Subalgebra`
  analogue of `Subring.tensorSquareMap`.
* `Subalgebra.tensorSquareMap_injective`: it is injective when `A` is flat over the domain `R`
  and `K`-balanced and `R`-balanced tensors in `H ⊗ H` agree
  (`TensorProduct.CompatibleSMul R K H H`), for instance when `K` is the fraction field of `R`.
* `Subalgebra.isBaseChange_val`: when `A` spans `H` over a localization `K` of `R`, the
  inclusion `A → H` is the base change of `A` to `K`;
  `Subalgebra.map_algEquiv_tensorTensorTensorComm_one_tmul` compares its tensor square with
  `tensorSquareMap`.
* `Subalgebra.tensorCubeMap`: the canonical map `A ⊗[R] (A ⊗[R] A) → H ⊗[K] (H ⊗[K] H)`, with
  `Subalgebra.tensorCubeMap_injective` for flat `A` and `Subalgebra.tensorCubeMap_assoc_tmul`
  relating the associators.
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
factors: it is the tensor square of the inclusion of `A`, followed by the quotient map
`H ⊗[R] H → H ⊗[K] H`. -/
noncomputable def tensorSquareMap (A : Subalgebra R H) : A ⊗[R] A →ₐ[R] H ⊗[K] H :=
  (Algebra.TensorProduct.mapOfCompatibleSMul K R R H H).comp
    (Algebra.TensorProduct.map A.val A.val)

/-- The canonical map `A ⊗[R] A → H ⊗[K] H` sends `x ⊗ y` to `x ⊗ y`. -/
@[simp]
theorem tensorSquareMap_tmul (A : Subalgebra R H) (x y : A) :
    tensorSquareMap K A (x ⊗ₜ y) = (x : H) ⊗ₜ[K] (y : H) := by
  simp [tensorSquareMap]

/-- An `R`-subalgebra `A` of an algebra `H` over a localization `K` of `R` at a submonoid `M`
which spans `H` over `K` has `H` as its localization at `M`: the inclusion `A → H` is the base
change of `A` to `K`. -/
theorem isBaseChange_val (M : Submonoid R) [IsLocalization M K] (A : Subalgebra R H)
    (hspan : Submodule.span K (A : Set H) = ⊤) :
    IsBaseChange K (A.val.toLinearMap : A →ₗ[R] H) :=
  (isLocalizedModule_iff_isBaseChange M K _).mp
    (A.toSubmodule.isLocalizedModule_subtype_of_span_eq_top M hspan)

/-- The tensor square of the base-change isomorphism `K ⊗[R] A ≃ H` of a spanning subalgebra,
applied to `(1 ⊗ 1) ⊗ t`, is the canonical image of `t ∈ A ⊗[R] A` in `H ⊗[K] H`. -/
theorem map_algEquiv_tensorTensorTensorComm_one_tmul (M : Submonoid R) [IsLocalization M K]
    (A : Subalgebra R H) (hspan : Submodule.span K (A : Set H) = ⊤) (t : A ⊗[R] A) :
    Algebra.TensorProduct.map (A.isBaseChange_val M hspan).algEquiv.toAlgHom
        (A.isBaseChange_val M hspan).algEquiv.toAlgHom
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K A A
        (((1 : K) ⊗ₜ[K] (1 : K)) ⊗ₜ[R] t)) = tensorSquareMap K A t := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
  | tmul x y => simp

variable (K) in
/-- The canonical map `A ⊗[R] (A ⊗[R] A) → H ⊗[K] (H ⊗[K] H)` for an `R`-subalgebra `A` of a
`K`-algebra `H`. On pure tensors it applies the inclusion of `A` and `tensorSquareMap`. -/
noncomputable def tensorCubeMap (A : Subalgebra R H) : A ⊗[R] (A ⊗[R] A) →ₗ[R] H ⊗[K] (H ⊗[K] H) :=
  TensorProduct.mapOfCompatibleSMul K R R H (H ⊗[K] H) ∘ₗ
    TensorProduct.map A.val.toLinearMap (tensorSquareMap K A).toLinearMap

/-- The canonical map `A ⊗[R] (A ⊗[R] A) → H ⊗[K] (H ⊗[K] H)` on pure tensors. -/
@[simp]
theorem tensorCubeMap_tmul (A : Subalgebra R H) (x : A) (t : A ⊗[R] A) :
    tensorCubeMap K A (x ⊗ₜ t) = (x : H) ⊗ₜ[K] tensorSquareMap K A t := by
  rw [tensorCubeMap, LinearMap.comp_apply, TensorProduct.map_tmul,
    TensorProduct.mapOfCompatibleSMul_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    Subalgebra.coe_val]

/-- The canonical map `A ⊗[R] (A ⊗[R] A) → H ⊗[K] (H ⊗[K] H)` intertwines the associators. -/
theorem tensorCubeMap_assoc_tmul (A : Subalgebra R H) (t : A ⊗[R] A) (z : A) :
    tensorCubeMap K A (Algebra.TensorProduct.assoc R R R A A A (t ⊗ₜ z)) =
      TensorProduct.assoc K H H H (tensorSquareMap K A t ⊗ₜ (z : H)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
  | tmul x y => simp

end Semiring

variable {R K H : Type*} [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [Ring H]
  [Algebra K H] [Algebra R H] [IsScalarTower R K H]

/-- For a flat `R`-subalgebra `A` of a `K`-algebra `H` over the domain `R`, the canonical map
`A ⊗[R] A → H ⊗[K] H` is injective as soon as `K`-balanced and `R`-balanced tensors in `H ⊗ H`
agree, for instance when `K` is the fraction field of `R`
(`IsLocalization.tensorProduct_compatibleSMul`). -/
-- Composed with the isomorphism `H ⊗[K] H ≅ H ⊗[R] H` of a localization, it is the tensor square
-- of the inclusion of `A`, which is injective since `A` is flat over the domain `R`.
theorem tensorSquareMap_injective [TensorProduct.CompatibleSMul R K H H] (A : Subalgebra R H)
    [Module.Flat R A] : Function.Injective (tensorSquareMap K A) := by
  have hcomp : (TensorProduct.mapOfCompatibleSMul R K R H H : H ⊗[K] H →ₗ[R] H ⊗[R] H) ∘ₗ
      (tensorSquareMap K A).toLinearMap =
        TensorProduct.map A.val.toLinearMap A.val.toLinearMap :=
    TensorProduct.ext' fun x y ↦ by simp
  refine .of_comp (f := TensorProduct.mapOfCompatibleSMul R K R H H) ?_
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.coe_comp, hcomp]
  exact TensorProduct.map_injective_of_flat_flat_of_isDomain _ _
    Subtype.val_injective Subtype.val_injective

/-- For a flat `R`-subalgebra `A` of a `K`-algebra `H` over the domain `R`, the canonical map
`A ⊗[R] (A ⊗[R] A) → H ⊗[K] (H ⊗[K] H)` is injective when `K`-balanced and `R`-balanced tensors
agree in `H ⊗ H`, for instance when `K` is the fraction field of `R`. -/
theorem tensorCubeMap_injective [TensorProduct.CompatibleSMul R K H H] (A : Subalgebra R H)
    [Module.Flat R A] : Function.Injective (tensorCubeMap K A) := by
  refine (TensorProduct.equivOfCompatibleSMul R K R H (H ⊗[K] H)).symm.injective.comp ?_
  exact TensorProduct.map_injective_of_flat_flat_of_isDomain _ _
    Subtype.val_injective (tensorSquareMap_injective A)

end Subalgebra
