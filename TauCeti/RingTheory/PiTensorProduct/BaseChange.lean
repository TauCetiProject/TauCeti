/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul

/-!
# Base change of finite tensor products of commutative algebras

For a finite family of commutative `R`-algebras `A i` and a commutative `R`-algebra `T`, scalar
extension commutes with the tensor product of the family:

  `T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`,   `t ⊗ (⨂ₜ aᵢ) ↦ t • ⨂ₜ (1 ⊗ aᵢ)`.

Geometrically, the fibre product over `Spec R` of the `Spec (A i)` pulls back to the fibre
product over `Spec T` of their base changes. Both sides are coproducts of commutative algebras, so
the equivalence is determined by the factor inclusions
(`PiTensorProduct.baseChangeAlgEquiv_tmul_singleAlgHom`).

## Main definitions

* `PiTensorProduct.baseChangeAlgEquiv`: the base change equivalence.

## Main results

* `PiTensorProduct.baseChangeAlgEquiv_tmul_tprod`,
  `PiTensorProduct.baseChangeAlgEquiv_symm_tprod_tmul`: its values and those of its inverse on pure
  tensors.
* `PiTensorProduct.baseChangeAlgEquiv_map_reindexAlgEquiv`: base change commutes with reindexing
  the factors; for a tensor power, with permuting them
  (`PiTensorProduct.baseChangeAlgEquiv_map_permAlgEquiv`).
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] (T : Type*) [CommSemiring T] [Algebra R T]
  {ι : Type*} (A : ι → Type*) [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]

section Aux

variable [Fintype ι] [DecidableEq ι]

/-- The `R`-algebra map `⨂[R] i, A i → ⨂[T] i, (T ⊗[R] A i)` placing each factor `aᵢ` as `1 ⊗ aᵢ`
in its own slot. -/
private noncomputable abbrev toBaseChange : (⨂[R] i, A i) →ₐ[R] ⨂[T] i, (T ⊗[R] A i) :=
  productMap fun i ↦ ((singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i).restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The `T`-algebra map `⨂[T] i, (T ⊗[R] A i) → T ⊗[R] (⨂[R] i, A i)` sending `t ⊗ aᵢ` in the
slot `i` to `t ⊗ aᵢ` with `aᵢ` in the slot `i`. -/
private noncomputable abbrev ofBaseChange : (⨂[T] i, (T ⊗[R] A i)) →ₐ[T] T ⊗[R] (⨂[R] i, A i) :=
  productMap fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i)

/-- `PiTensorProduct.baseChangeAlgEquiv`, for a chosen enumeration and decidable equality of the
index type. -/
private noncomputable def baseChangeAlgEquivAux :
    T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i) :=
  AlgEquiv.ofAlgHom (AlgHom.liftEquiv R T _ _ (toBaseChange T A)) (ofBaseChange T A)
    (algHom_ext fun i ↦ Algebra.TensorProduct.ext_ring <| AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
      rw [productMap_singleAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.liftEquiv_tmul, one_smul, productMap_singleAlgHom, AlgHom.comp_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply])
    (Algebra.TensorProduct.ext_ring <| algHom_ext fun i ↦ AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
      rw [AlgHom.liftEquiv_tmul, one_smul, productMap_singleAlgHom, AlgHom.comp_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        productMap_singleAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply])

end Aux

/-- Scalar extension commutes with finite tensor products of commutative algebras:
`T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`, sending `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
noncomputable def baseChangeAlgEquiv [Finite ι] :
    T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i) :=
  letI := Fintype.ofFinite ι
  letI := Classical.decEq ι
  baseChangeAlgEquivAux T A

/-- `PiTensorProduct.baseChangeAlgEquiv` does not depend on the instances chosen to construct it. -/
private theorem baseChangeAlgEquiv_eq_aux [Fintype ι] [DecidableEq ι] :
    baseChangeAlgEquiv (R := R) T A = baseChangeAlgEquivAux T A := by
  rw [baseChangeAlgEquiv]
  congr!

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul_tprod [Finite ι] (t : T) (x : ∀ i, A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ tprod R x) = t • tprod T fun i ↦ (1 : T) ⊗ₜ[R] x i := by
  have := Fintype.ofFinite ι
  classical
  rw [baseChangeAlgEquiv_eq_aux, baseChangeAlgEquivAux, AlgEquiv.ofAlgHom_apply,
    AlgHom.liftEquiv_tmul, productMap_tprod, tprod_eq_prod_singleAlgHom]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a`, with `a` in the slot `i`, to `t ⊗ a` in the
slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_tmul_singleAlgHom [Finite ι] [DecidableEq ι] (t : T) (i : ι)
    (a : A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ singleAlgHom i a) =
      singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i (t ⊗ₜ a) := by
  have := Fintype.ofFinite ι
  rw [baseChangeAlgEquiv_eq_aux, baseChangeAlgEquivAux, AlgEquiv.ofAlgHom_apply,
    AlgHom.liftEquiv_tmul, productMap_singleAlgHom, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The inverse of `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a` in the slot `i` to `t ⊗ a`,
with `a` in the slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_symm_singleAlgHom [Finite ι] [DecidableEq ι] (i : ι)
    (x : T ⊗[R] A i) :
    (baseChangeAlgEquiv T A).symm (singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i x) =
      Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i) x := by
  have := Fintype.ofFinite ι
  rw [baseChangeAlgEquiv_eq_aux, baseChangeAlgEquivAux, AlgEquiv.ofAlgHom_symm,
    AlgEquiv.ofAlgHom_apply, productMap_singleAlgHom]

/-- The inverse of `PiTensorProduct.baseChangeAlgEquiv` sends `⨂ₜ (tᵢ ⊗ aᵢ)` to
`(∏ᵢ tᵢ) ⊗ (⨂ₜ aᵢ)`. -/
@[simp]
theorem baseChangeAlgEquiv_symm_tprod_tmul [Fintype ι] (t : ι → T) (x : ∀ i, A i) :
    (baseChangeAlgEquiv T A).symm (tprod T fun i ↦ t i ⊗ₜ[R] x i) = (∏ i, t i) ⊗ₜ[R] tprod R x := by
  rw [AlgEquiv.symm_apply_eq, baseChangeAlgEquiv_tmul_tprod, ← MultilinearMap.map_smul_univ]
  congr 1
  funext i
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Base change commutes with reindexing the factors. -/
theorem baseChangeAlgEquiv_map_reindexAlgEquiv {κ : Type*} [Finite ι] [Finite κ] (e : ι ≃ κ)
    (x : T ⊗[R] (⨂[R] i, A i)) :
    baseChangeAlgEquiv T (fun j ↦ A (e.symm j))
        (Algebra.TensorProduct.map (AlgHom.id T T) (reindexAlgEquiv A e).toAlgHom x) =
      reindexAlgEquiv (fun i ↦ T ⊗[R] A i) e (baseChangeAlgEquiv T A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      generalize r • t = t
      simp
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Base change commutes with permuting the factors of a tensor power. -/
theorem baseChangeAlgEquiv_map_permAlgEquiv [Finite ι] {B : Type*} [CommSemiring B] [Algebra R B]
    (σ : Equiv.Perm ι) (x : T ⊗[R] (⨂[R] _ : ι, B)) :
    baseChangeAlgEquiv T (fun _ ↦ B)
        (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv B σ).toAlgHom x) =
      permAlgEquiv (T ⊗[R] B) σ (baseChangeAlgEquiv T (fun _ ↦ B) x) := by
  rw [permAlgEquiv_eq_reindexAlgEquiv, permAlgEquiv_eq_reindexAlgEquiv]
  exact baseChangeAlgEquiv_map_reindexAlgEquiv T (fun _ ↦ B) σ x

end PiTensorProduct
