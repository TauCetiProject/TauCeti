/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.RingTheory.PiTensorProduct.Basic

/-!
# Factorwise algebra homomorphisms and product maps on indexed tensor products

Given families of `R`-algebras `A` and `B` indexed by `ι`, a family of `R`-algebra homomorphisms
`f : ∀ i, A i →ₐ[R] B i` induces an `R`-algebra homomorphism on the indexed tensor product
`⨂[R] i, A i →ₐ[R] ⨂[R] i, B i`, upgrading `PiTensorProduct.map` from linear maps to algebra maps
and matching `Algebra.TensorProduct.map` for binary tensor products.

We record functoriality of `PiTensorProduct.mapAlgHom` and show that applying `LinearMap.mul` in
every factor via `PiTensorProduct.map₂` recovers multiplication on the indexed tensor product.

Algebra maps `f j : A j → S` out of a finite family of `R`-algebras into a commutative algebra
`S` induce `PiTensorProduct.productMap f : (⨂[R] j, A j) →ₐ[R] S`, sending `⨂ₜ xⱼ` to
`∏ⱼ f j (x j)`. Every algebra map from `⨂[R] j, A j` to a commutative algebra arises this way from
its restrictions to the factors; in particular, a finite tensor product of commutative algebras
is their coproduct. This is the indexed analogue of `Algebra.TensorProduct.productMap`.

## Main definitions

* `PiTensorProduct.mapAlgHom`: the `R`-algebra homomorphism `(⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i`
  induced by a family `f : ∀ i, A i →ₐ[R] B i`.
* `PiTensorProduct.productMap`: the algebra map out of a finite tensor product of algebras into a
  commutative algebra induced by algebra maps out of the factors.

## Main results

* `PiTensorProduct.mapAlgHom_tprod`, `PiTensorProduct.mapAlgHom_singleAlgHom`: action of
  `mapAlgHom` on pure tensors and factor inclusions.
* `PiTensorProduct.mapAlgHom_id`, `PiTensorProduct.mapAlgHom_comp`,
  `PiTensorProduct.mapAlgHom_mapAlgHom`: functoriality of `mapAlgHom`.
* `PiTensorProduct.map₂_mul_apply`: applying `LinearMap.mul` in each factor via
  `PiTensorProduct.map₂` (`PiTensorProduct.map₂_mul`) to two tensors multiplies them.
* `PiTensorProduct.productMap_tprod`, `PiTensorProduct.productMap_singleAlgHom`: the values of
  `PiTensorProduct.productMap` on pure tensors and on the factor inclusions.
* `PiTensorProduct.productMap_comp_singleAlgHom'`, `PiTensorProduct.comp_productMap`: an algebra
  map into a commutative algebra is the product map of its restrictions to the factors, and
  postcomposition acts factorwise.
* `PiTensorProduct.productMap_comp_mapAlgHom`: precomposition with `PiTensorProduct.mapAlgHom`
  acts factorwise.
* `PiTensorProduct.productMap_reindex`: invariance of `PiTensorProduct.productMap` under
  reindexing.
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

section ProductMap

variable {τ : Type*} {A : τ → Type*} [∀ j, Semiring (A j)] [∀ j, Algebra R (A j)]
  [Fintype τ] {S : Type*} [CommSemiring S] [Algebra R S]

/-- The algebra map `⨂[R] j, A j → S` induced by algebra maps `f j : A j → S` into a commutative
algebra: it sends `⨂ₜ xⱼ` to `∏ⱼ f j (x j)`. Every algebra map from `⨂[R] j, A j` to a commutative
algebra arises this way from its restrictions to the factors
(`PiTensorProduct.productMap_comp_singleAlgHom'`, uniqueness by `PiTensorProduct.algHom_ext`); in
particular a finite tensor product of commutative algebras is their coproduct. It is the indexed
analogue of `Algebra.TensorProduct.productMap`. -/
noncomputable def productMap (f : ∀ j, A j →ₐ[R] S) : (⨂[R] j, A j) →ₐ[R] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra R τ S).compLinearMap fun j ↦ (f j).toLinearMap)
    (by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.one_apply, map_one, Finset.prod_const_one])
    (fun x y ↦ by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib])

/-- `PiTensorProduct.productMap f` sends a pure tensor to the product of the images of its
factors. -/
@[simp]
theorem productMap_tprod (f : ∀ j, A j →ₐ[R] S) (x : ∀ j, A j) :
    productMap f (tprod R x) = ∏ j, f j (x j) :=
  -- `lift.tprod` evaluates the multilinear map, which is the product by definition.
  (liftAlgHom_apply _ _ _ _).trans (lift.tprod _)

/-- `PiTensorProduct.productMap f` restricts to `f j` on the factor inclusion at `j`. It is a
pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem productMap_singleAlgHom [DecidableEq τ] (f : ∀ j, A j →ₐ[R] S) (j : τ) (a : A j) :
    productMap f (singleAlgHom j a) = f j a := by
  simp only [singleAlgHom_apply, productMap_tprod, MonoidHom.mulSingle_apply,
    Pi.apply_mulSingle (fun k ↦ ⇑(f k)) (fun k ↦ map_one (f k)), Fintype.prod_pi_mulSingle']

/-- `PiTensorProduct.productMap f` restricts to `f j` along the factor inclusion at `j`. -/
@[simp]
theorem productMap_comp_singleAlgHom [DecidableEq τ] (f : ∀ j, A j →ₐ[R] S) (j : τ) :
    (productMap f).comp (singleAlgHom j) = f j :=
  AlgHom.ext (productMap_singleAlgHom f j)

/-- An algebra map from `⨂[R] j, A j` to a commutative algebra is the product map of its
restrictions to the factors. -/
@[simp]
theorem productMap_comp_singleAlgHom' [DecidableEq τ] (g : (⨂[R] j, A j) →ₐ[R] S) :
    productMap (fun j ↦ g.comp (singleAlgHom j)) = g :=
  algHom_ext fun j ↦ productMap_comp_singleAlgHom _ j

/-- Postcomposing `PiTensorProduct.productMap f` with an algebra map into another commutative
algebra postcomposes each factor map. -/
@[simp]
theorem comp_productMap {T : Type*} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T)
    (f : ∀ j, A j →ₐ[R] S) : h.comp (productMap f) = productMap fun j ↦ h.comp (f j) := by
  classical
  exact algHom_ext fun j ↦ by
    rw [AlgHom.comp_assoc, productMap_comp_singleAlgHom, productMap_comp_singleAlgHom]

/-- Precomposing `PiTensorProduct.productMap g` with the factorwise map
`PiTensorProduct.mapAlgHom f` precomposes each factor map. -/
@[simp]
theorem productMap_comp_mapAlgHom {B : τ → Type*} [∀ j, Semiring (B j)] [∀ j, Algebra R (B j)]
    (g : ∀ j, B j →ₐ[R] S) (f : ∀ j, A j →ₐ[R] B j) :
    (productMap g).comp (mapAlgHom f) = productMap fun j ↦ (g j).comp (f j) := by
  classical
  exact algHom_ext fun j ↦ AlgHom.ext fun a ↦ by
    simp only [AlgHom.comp_apply, mapAlgHom_singleAlgHom, productMap_singleAlgHom]

/-- `PiTensorProduct.productMap` is invariant under reindexing the factors along a bijection. -/
@[simp]
theorem productMap_reindex {τ' : Type*} [Fintype τ'] (e : τ ≃ τ') (f : ∀ j, A j →ₐ[R] S)
    (x : ⨂[R] j, A j) :
    productMap (fun k ↦ f (e.symm k)) (reindex R A e x) = productMap f x := by
  refine (liftAlgHom_apply _ _ _ _).trans <| (lift_reindex e _ x).trans <|
    .trans ?_ (liftAlgHom_apply _ _ _ _).symm
  congr 1
  ext a
  simp [e.symm.prod_comp fun j ↦ f j (a j)]

end ProductMap

end PiTensorProduct
