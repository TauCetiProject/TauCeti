/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.RingTheory.PiTensorProduct.Basic

/-!
# Factorwise algebra homomorphisms on indexed tensor products

Given families of `R`-algebras `A` and `B` indexed by `ι`, a family of `R`-algebra homomorphisms
`f : ∀ i, A i →ₐ[R] B i` induces an `R`-algebra homomorphism on the indexed tensor product
`⨂[R] i, A i →ₐ[R] ⨂[R] i, B i`, upgrading `PiTensorProduct.map` from linear maps to algebra maps
and matching `Algebra.TensorProduct.map` for binary tensor products.

We record functoriality of `PiTensorProduct.mapAlgHom` and show that applying `LinearMap.mul` in
every factor via `PiTensorProduct.map₂` recovers multiplication on the indexed tensor product.

## Main definitions

* `PiTensorProduct.mapAlgHom`: the `R`-algebra homomorphism `(⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i`
  induced by a family `f : ∀ i, A i →ₐ[R] B i`.

## Main results

* `PiTensorProduct.mapAlgHom_tprod`, `PiTensorProduct.mapAlgHom_singleAlgHom`: action of
  `mapAlgHom` on pure tensors and factor inclusions.
* `PiTensorProduct.mapAlgHom_id`, `PiTensorProduct.mapAlgHom_comp`,
  `PiTensorProduct.mapAlgHom_mapAlgHom`: functoriality of `mapAlgHom`.
* `PiTensorProduct.map₂_mul_apply`: applying `LinearMap.mul` in each factor via
  `PiTensorProduct.map₂` (`PiTensorProduct.map₂_mul`) to two tensors multiplies them.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

section Map

variable {ι : Type*} {A B C : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)] [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]

/-- A family of `R`-algebra homomorphisms `f i : A i →ₐ[R] B i` induces an `R`-algebra
homomorphism on the indexed tensor product, sending `⨂ₜ aᵢ` to `⨂ₜ fᵢ aᵢ`.

This upgrades `PiTensorProduct.map` to `AlgHom`. -/
noncomputable def mapAlgHom (f : ∀ i, A i →ₐ[R] B i) : (⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i :=
  liftAlgHom ((tprod R).compLinearMap fun i ↦ (f i).toLinearMap) (by simp [one_def, Pi.one_def])
    (fun x y ↦ by simp [tprod_mul_tprod, Pi.mul_def])

/-- The underlying linear map of `PiTensorProduct.mapAlgHom` is `PiTensorProduct.map`. -/
@[simp]
theorem mapAlgHom_toLinearMap (f : ∀ i, A i →ₐ[R] B i) :
    (mapAlgHom f).toLinearMap = map fun i ↦ (f i).toLinearMap := (rfl)

/-- `PiTensorProduct.mapAlgHom` applies each algebra map to the corresponding entry of a pure
tensor. -/
@[simp]
theorem mapAlgHom_tprod (f : ∀ i, A i →ₐ[R] B i) (a : ∀ i, A i) :
    mapAlgHom f (tprod R a) = tprod R fun i ↦ f i (a i) := by
  simp [mapAlgHom]

/-- `PiTensorProduct.mapAlgHom` acts on the factor inclusion at `i` by applying `f i` in slot `i`.
It is a pre-simp lemma since `singleAlgHom_apply` would otherwise unfold the factor inclusion
first. -/
@[simp↓]
theorem mapAlgHom_singleAlgHom [DecidableEq ι] (f : ∀ i, A i →ₐ[R] B i) (i : ι) (a : A i) :
    mapAlgHom f (singleAlgHom i a) = singleAlgHom i (f i a) := by
  rw [singleAlgHom_apply, singleAlgHom_apply, mapAlgHom_tprod]
  congr 1 with j
  rcases eq_or_ne j i with rfl | hji <;> simp [Pi.mulSingle_eq_of_ne, *]

variable (R A) in
/-- `PiTensorProduct.mapAlgHom` of the identity family is the identity algebra homomorphism. -/
@[simp]
theorem mapAlgHom_id : mapAlgHom (fun i ↦ AlgHom.id R (A i)) = AlgHom.id R (⨂[R] i, A i) :=
  AlgHom.toLinearMap_injective <| by simp [AlgHom.toLinearMap_id]

/-- `PiTensorProduct.mapAlgHom` respects slotwise composition of algebra homomorphisms. -/
theorem mapAlgHom_comp (g : ∀ i, B i →ₐ[R] C i) (f : ∀ i, A i →ₐ[R] B i) :
    mapAlgHom (fun i ↦ (g i).comp (f i)) = (mapAlgHom g).comp (mapAlgHom f) :=
  AlgHom.toLinearMap_injective <|
    map_comp (fun i ↦ (g i).toLinearMap) (fun i ↦ (f i).toLinearMap)

/-- Applying two `PiTensorProduct.mapAlgHom` maps in succession composes them in each slot. -/
theorem mapAlgHom_mapAlgHom (g : ∀ i, B i →ₐ[R] C i) (f : ∀ i, A i →ₐ[R] B i) (x : ⨂[R] i, A i) :
    mapAlgHom g (mapAlgHom f x) = mapAlgHom (fun i ↦ (g i).comp (f i)) x :=
  DFunLike.congr_fun (mapAlgHom_comp g f).symm x

/-- Applying `PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` to two tensors multiplies
them. -/
theorem map₂_mul_apply (x y : ⨂[R] i, A i) : map₂ (fun i ↦ LinearMap.mul R (A i)) x y = x * y := by
  rw [map₂_mul, LinearMap.mul_apply']

end Map

end PiTensorProduct
