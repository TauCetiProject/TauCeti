/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.PiTensorProduct.Equiv

/-!
# Base change of finite tensor products of algebras

For a finite family of `R`-algebras `A i` and a commutative `R`-algebra `T`, scalar extension
commutes with the tensor product of the family:

  `T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`,   `t ⊗ (⨂ₜ aᵢ) ↦ t • ⨂ₜ (1 ⊗ aᵢ)`.

For commutative algebras, geometrically, the fibre product over `Spec R` of the `Spec (A i)` pulls
back to the fibre product over `Spec T` of their base changes. The algebras `A i` need not be
commutative: the equivalence is built by induction on the finite index type from the binary
base change `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`. On the factor inclusions
it is `t ⊗ a ↦ t ⊗ a` (`PiTensorProduct.baseChangeAlgEquiv_tmul_singleAlgHom`).

## Main definitions

* `PiTensorProduct.baseChangeAlgEquiv`: the base change equivalence.

## Main results

* `PiTensorProduct.baseChangeAlgEquiv_tmul_tprod`,
  `PiTensorProduct.baseChangeAlgEquiv_symm_tprod_tmul`: its values and those of its inverse on pure
  tensors.
* `PiTensorProduct.baseChangeAlgEquiv_map_reindexAlgEquiv`: base change commutes with reindexing
  the factors; for a tensor power, with permuting them
  (`PiTensorProduct.baseChangeAlgEquiv_map_permAlgEquiv`).
* `PiTensorProduct.baseChangeAlgEquiv_map_congrAlgEquiv`: base change commutes with applying
  algebra equivalences factorwise.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] (T : Type w) [CommSemiring T] [Algebra R T]

/-- An equivalence `T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)` with the expected values on
pure tensors exists, by induction on the finite index type. -/
private theorem exists_baseChangeAlgEquiv (ι : Type x) [Finite ι] :
    ∀ (A : ι → Type v) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)],
      ∃ e : T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i),
        ∀ (t : T) (a : ∀ i, A i), e (t ⊗ₜ tprod R a) = t • tprod T fun i ↦ (1 : T) ⊗ₜ[R] a i := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro A _ _
    obtain ⟨f, hf⟩ := ih fun i ↦ A (e i)
    refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl (reindexAlgEquiv A e.symm)).trans
      (f.trans (reindexAlgEquiv (fun i ↦ T ⊗[R] A i) e.symm).symm), fun t a ↦ ?_⟩
    simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      reindexAlgEquiv_tprod, hf, map_smul]
    exact congrArg (t • ·) (reindexAlgEquiv_symm_tprod _ e.symm fun i ↦ (1 : T) ⊗ₜ[R] a i)
  | h_empty =>
    intro A _ _
    refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl (isEmptyAlgEquiv PEmpty A)).trans
      ((Algebra.TensorProduct.rid R T T).trans (isEmptyAlgEquiv PEmpty _).symm), fun t a ↦ ?_⟩
    simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      isEmptyAlgEquiv_tprod, Algebra.TensorProduct.rid_tmul, one_smul, isEmptyAlgEquiv_symm_apply]
    exact congrArg (t • ·) ((isEmptyAlgEquiv (R := T) PEmpty _).injective (by simp))
  | @h_option α _ ih =>
    intro A _ _
    obtain ⟨f, hf⟩ := ih fun i ↦ A (some i)
    refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl (optionAlgEquiv A)).trans
      ((TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv R T _ _).trans
        ((Algebra.TensorProduct.congr f AlgEquiv.refl).trans
          (optionAlgEquiv fun o ↦ T ⊗[R] A o).symm)), fun t a ↦ ?_⟩
    simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      optionAlgEquiv_tprod, TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul, hf,
      ← TensorProduct.smul_tmul', map_smul]
    exact congrArg (t • ·) (optionAlgEquiv_symm_tmul _ fun o ↦ (1 : T) ⊗ₜ[R] a o)

variable {ι : Type x} (A : ι → Type v) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- Scalar extension commutes with finite tensor products of algebras:
`T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`, sending `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`.
The algebras `A i` need not be commutative. The equivalence is characterized by its values on pure
tensors (`PiTensorProduct.baseChangeAlgEquiv_tmul_tprod`). -/
noncomputable def baseChangeAlgEquiv [Finite ι] :
    T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i) :=
  (exists_baseChangeAlgEquiv T ι A).choose

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul_tprod [Finite ι] (t : T) (x : ∀ i, A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ tprod R x) = t • tprod T fun i ↦ (1 : T) ⊗ₜ[R] x i :=
  (exists_baseChangeAlgEquiv T ι A).choose_spec t x

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a`, with `a` in the slot `i`, to `t ⊗ a` in the
slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_tmul_singleAlgHom [Finite ι] [DecidableEq ι] (t : T) (i : ι)
    (a : A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ singleAlgHom i a) =
      singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i (t ⊗ₜ a) := by
  rw [singleAlgHom_apply, baseChangeAlgEquiv_tmul_tprod, TensorProduct.tmul_eq_smul_one_tmul t a,
    map_smul, singleAlgHom_apply]
  congr 2
  exact (Pi.mulSingle_op (fun j ↦ ((1 : T) ⊗ₜ[R] · : A j → T ⊗[R] A j))
    (fun _ ↦ Algebra.TensorProduct.one_def.symm) i a).symm

/-- The inverse of `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a` in the slot `i` to `t ⊗ a`,
with `a` in the slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_symm_singleAlgHom [Finite ι] [DecidableEq ι] (i : ι)
    (x : T ⊗[R] A i) :
    (baseChangeAlgEquiv T A).symm (singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i x) =
      Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i) x := by
  rw [AlgEquiv.symm_apply_eq]
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeAlgEquiv_tmul_singleAlgHom]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

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

/-- Base change commutes with applying algebra equivalences factorwise. -/
theorem baseChangeAlgEquiv_map_congrAlgEquiv [Finite ι] {B : ι → Type*} [∀ i, Semiring (B i)]
    [∀ i, Algebra R (B i)] (e : ∀ i, A i ≃ₐ[R] B i) (x : T ⊗[R] (⨂[R] i, A i)) :
    baseChangeAlgEquiv T B
        (Algebra.TensorProduct.map (AlgHom.id T T) (congrAlgEquiv e).toAlgHom x) =
      congrAlgEquiv (fun i ↦ Algebra.TensorProduct.congr AlgEquiv.refl (e i))
        (baseChangeAlgEquiv T A x) := by
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
theorem baseChangeAlgEquiv_map_permAlgEquiv [Finite ι] {B : Type*} [Semiring B] [Algebra R B]
    (σ : Equiv.Perm ι) (x : T ⊗[R] (⨂[R] _ : ι, B)) :
    baseChangeAlgEquiv T (fun _ ↦ B)
        (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv B σ).toAlgHom x) =
      permAlgEquiv (T ⊗[R] B) σ (baseChangeAlgEquiv T (fun _ ↦ B) x) := by
  rw [permAlgEquiv_eq_reindexAlgEquiv, permAlgEquiv_eq_reindexAlgEquiv]
  exact baseChangeAlgEquiv_map_reindexAlgEquiv T (fun _ ↦ B) σ x

end PiTensorProduct
