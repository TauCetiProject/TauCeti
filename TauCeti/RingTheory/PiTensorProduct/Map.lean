/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul

/-!
# Factorwise algebra homomorphisms on indexed tensor products

Given families of `R`-algebras `A` and `B` indexed by `ι`, a family of `R`-algebra homomorphisms
`f : ∀ i, A i →ₐ[R] B i` induces an `R`-algebra homomorphism on the indexed tensor product
`⨂[R] i, A i →ₐ[R] ⨂[R] i, B i`, upgrading `PiTensorProduct.map` from linear maps to algebra maps
and matching `Algebra.TensorProduct.map` for binary tensor products.

We also relate `PiTensorProduct.mapAlgHom` to `PiTensorProduct.congrAlgEquiv`, record functoriality
and commutation with `PiTensorProduct.reindexAlgEquiv`, and show that `PiTensorProduct.mulAlgHom`
is invariant under reindexing and permutations of the tensor factors.

## Main definitions

* `PiTensorProduct.mapAlgHom`: the `R`-algebra homomorphism `(⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i`
  induced by a family `f : ∀ i, A i →ₐ[R] B i`.

## Main results

* `PiTensorProduct.mapAlgHom_tprod`, `PiTensorProduct.mapAlgHom_singleAlgHom`: action of
  `mapAlgHom` on pure tensors and factor inclusions.
* `PiTensorProduct.mapAlgHom_id`, `PiTensorProduct.mapAlgHom_comp`: functoriality of `mapAlgHom`.
* `PiTensorProduct.congrAlgEquiv_toAlgHom`, `PiTensorProduct.congrAlgEquiv_symm`,
  `PiTensorProduct.congrAlgEquiv_refl`, `PiTensorProduct.congrAlgEquiv_trans`: compatibility and
  groupoid API for `PiTensorProduct.congrAlgEquiv`.
* `PiTensorProduct.reindexAlgEquiv_mapAlgHom`,
  `PiTensorProduct.reindexAlgEquiv_trans_congrAlgEquiv`: commutation of reindexing with factorwise
  algebra maps and equivalences.
* `PiTensorProduct.mulAlgHom_reindexAlgEquiv`, `PiTensorProduct.mulAlgHom_permAlgEquiv`:
  invariance of `PiTensorProduct.mulAlgHom` under reindexing and permutations of a finite index
  type.
* `PiTensorProduct.map₂_mul`: applying `LinearMap.mul` in each factor via `PiTensorProduct.map₂`
  recovers multiplication on the indexed tensor product.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

section Map

variable {ι : Type*} {A B C : ι → Type*}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]

/-- A family of `R`-algebra homomorphisms `f i : A i →ₐ[R] B i` induces an `R`-algebra
homomorphism on the indexed tensor product, sending `⨂ₜ aᵢ` to `⨂ₜ fᵢ aᵢ`.

This upgrades `PiTensorProduct.map` to `AlgHom`. -/
noncomputable def mapAlgHom (f : ∀ i, A i →ₐ[R] B i) :
    (⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i :=
  AlgHom.ofLinearMap (map fun i ↦ (f i).toLinearMap)
    (by simp [one_def, map_tprod, Pi.one_def]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext a b
      simp [tprod_mul_tprod, map_tprod, Pi.mul_def]

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
  congr 1
  ext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [Pi.mulSingle_eq_of_ne hji]

variable (R A) in
/-- `PiTensorProduct.mapAlgHom` of the identity family is the identity algebra homomorphism. -/
@[simp]
theorem mapAlgHom_id :
    mapAlgHom (fun i ↦ AlgHom.id R (A i)) = AlgHom.id R (⨂[R] i, A i) :=
  AlgHom.toLinearMap_injective <| by simp [AlgHom.toLinearMap_id]

/-- `PiTensorProduct.mapAlgHom` respects slotwise composition of algebra homomorphisms. -/
theorem mapAlgHom_comp (g : ∀ i, B i →ₐ[R] C i) (f : ∀ i, A i →ₐ[R] B i) :
    mapAlgHom (fun i ↦ (g i).comp (f i)) = (mapAlgHom g).comp (mapAlgHom f) :=
  AlgHom.toLinearMap_injective <|
    map_comp (fun i ↦ (g i).toLinearMap) (fun i ↦ (f i).toLinearMap)

/-- Applying two `PiTensorProduct.mapAlgHom` maps in succession composes them in each slot. -/
theorem mapAlgHom_mapAlgHom (g : ∀ i, B i →ₐ[R] C i) (f : ∀ i, A i →ₐ[R] B i)
    (x : ⨂[R] i, A i) :
    mapAlgHom g (mapAlgHom f x) = mapAlgHom (fun i ↦ (g i).comp (f i)) x :=
  DFunLike.congr_fun (mapAlgHom_comp g f).symm x

/-- Reindexing an indexed tensor product commutes with applying a family of algebra maps in the
slots. -/
theorem reindexAlgEquiv_mapAlgHom {κ : Type*} (e : ι ≃ κ) (f : ∀ i, A i →ₐ[R] B i)
    (x : ⨂[R] i, A i) :
    reindexAlgEquiv B e (mapAlgHom f x) =
      mapAlgHom (fun j ↦ f (e.symm j)) (reindexAlgEquiv A e x) := by
  have h : (reindexAlgEquiv (R := R) B e).toAlgHom.comp (mapAlgHom f) =
      (mapAlgHom fun j ↦ f (e.symm j)).comp (reindexAlgEquiv (R := R) A e).toAlgHom :=
    AlgHom.toLinearMap_injective <| ext <| MultilinearMap.ext fun a ↦ by
      simp [AlgHom.comp_toLinearMap]
  exact DFunLike.congr_fun h x

/-- Applying `LinearMap.mul` in every slot via `PiTensorProduct.map₂` recovers multiplication on
`⨂[R] i, A i`. -/
@[simp]
theorem map₂_mul :
    map₂ (fun i ↦ LinearMap.mul R (A i)) = LinearMap.mul R (⨂[R] i, A i) := by
  refine ext <| MultilinearMap.ext fun x ↦ ext <| MultilinearMap.ext fun y ↦ ?_
  simp [map₂_tprod_tprod, tprod_mul_tprod, Pi.mul_def]

/-- Applying `PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` to two tensors multiplies
them. -/
theorem map₂_mul_apply (x y : ⨂[R] i, A i) :
    map₂ (fun i ↦ LinearMap.mul R (A i)) x y = x * y := by
  rw [map₂_mul, LinearMap.mul_apply']

end Map

section Congr

variable {ι : Type*} {A B C : ι → Type*}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]

/-- The underlying algebra homomorphism of `PiTensorProduct.congrAlgEquiv` is
`PiTensorProduct.mapAlgHom`. -/
@[simp]
theorem congrAlgEquiv_toAlgHom (f : ∀ i, A i ≃ₐ[R] B i) :
    (congrAlgEquiv f).toAlgHom = mapAlgHom fun i ↦ (f i).toAlgHom :=
  AlgHom.toLinearMap_injective <| ext <| MultilinearMap.ext fun a ↦ by simp

/-- The inverse of `PiTensorProduct.congrAlgEquiv` is `congrAlgEquiv` of the slotwise inverses. -/
@[simp]
theorem congrAlgEquiv_symm (f : ∀ i, A i ≃ₐ[R] B i) :
    (congrAlgEquiv f).symm = congrAlgEquiv fun i ↦ (f i).symm := by
  refine AlgEquiv.ext fun x ↦ (AlgEquiv.symm_apply_eq _).mpr ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r b => simp only [map_smul, congrAlgEquiv_tprod, AlgEquiv.apply_symm_apply]
  | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]

variable (R A) in
/-- `PiTensorProduct.congrAlgEquiv` of the identity equivalences is `AlgEquiv.refl`. -/
@[simp]
theorem congrAlgEquiv_refl :
    congrAlgEquiv (fun i ↦ AlgEquiv.refl (A₁ := A i) (R := R)) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| by simp

/-- `PiTensorProduct.congrAlgEquiv` respects slotwise transitivity of algebra equivalences. -/
theorem congrAlgEquiv_trans (f : ∀ i, A i ≃ₐ[R] B i) (g : ∀ i, B i ≃ₐ[R] C i) :
    congrAlgEquiv (fun i ↦ (f i).trans (g i)) = (congrAlgEquiv f).trans (congrAlgEquiv g) := by
  refine AlgEquiv.ext fun x ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Reindexing followed by slotwise algebra equivalences equals slotwise algebra equivalences
followed by reindexing. -/
theorem reindexAlgEquiv_trans_congrAlgEquiv {κ : Type*} (e : ι ≃ κ) (f : ∀ i, A i ≃ₐ[R] B i) :
    (reindexAlgEquiv (R := R) A e).trans (congrAlgEquiv fun j ↦ f (e.symm j)) =
      (congrAlgEquiv f).trans (reindexAlgEquiv (R := R) B e) := by
  refine AlgEquiv.ext fun x ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Congr

section MulAlgHom

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {B : Type*} [CommSemiring B] [Algebra R B]

/-- Multiplying the factors of a finite tensor power of a commutative algebra is invariant under
reindexing the factors along a bijection. -/
@[simp]
theorem mulAlgHom_reindex (e : σ ≃ τ) (x : ⨂[R] _ : σ, B) :
    mulAlgHom (R := R) (reindex R (fun _ ↦ B) e x) = mulAlgHom (R := R) x := by
  have h : (mulAlgHom (R := R) (σ := τ) (B := B)).toLinearMap ∘ₗ
      (reindex R (fun _ ↦ B) e).toLinearMap =
      (mulAlgHom (R := R) (σ := σ) (B := B)).toLinearMap :=
    ext <| MultilinearMap.ext fun b ↦ by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, reindex_tprod, mulAlgHom_tprod]
      exact e.symm.prod_comp b
  exact LinearMap.congr_fun h x

/-- `PiTensorProduct.mulAlgHom` is invariant under `PiTensorProduct.reindexAlgEquiv`. -/
@[simp]
theorem mulAlgHom_reindexAlgEquiv (e : σ ≃ τ) (x : ⨂[R] _ : σ, B) :
    mulAlgHom (R := R) (reindexAlgEquiv (R := R) (fun _ ↦ B) e x) = mulAlgHom (R := R) x := by
  rw [← AlgEquiv.toLinearEquiv_apply, reindexAlgEquiv_toLinearEquiv, mulAlgHom_reindex]

/-- Precomposing `PiTensorProduct.mulAlgHom` with `PiTensorProduct.reindexAlgEquiv` recovers
`PiTensorProduct.mulAlgHom`. -/
@[simp]
theorem mulAlgHom_comp_reindexAlgEquiv (e : σ ≃ τ) :
    (mulAlgHom (R := R) (σ := τ) (B := B)).comp
        (reindexAlgEquiv (R := R) (fun _ ↦ B) e).toAlgHom =
      mulAlgHom (R := R) (σ := σ) (B := B) :=
  AlgHom.ext <| mulAlgHom_reindexAlgEquiv e

/-- `PiTensorProduct.mulAlgHom` is invariant under permuting the factors of a finite tensor power
by `PiTensorProduct.permAlgEquiv`. -/
@[simp]
theorem mulAlgHom_permAlgEquiv (π : Equiv.Perm σ) (x : ⨂[R] _ : σ, B) :
    mulAlgHom (R := R) (permAlgEquiv (R := R) B π x) = mulAlgHom (R := R) x := by
  rw [← AlgEquiv.toLinearEquiv_apply, permAlgEquiv_toLinearEquiv, mulAlgHom_reindex]

end MulAlgHom

end PiTensorProduct
