/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Contracting two slots of an indexed tensor power

A bilinear form contracts two distinct slots of a tensor power and leaves the other slots
unchanged. The output is indexed by the complement of those two slots, avoiding a choice of
ordering on the remaining factors. For a finite index set of size `d`, this is a tensor power
with `d - 2` factors.

`LinearMap.contractTensorPair` is characterized on pure tensors and commutes with diagonal
maps preserving the pairing. These are the trace maps used to define harmonic tensors for
orthogonal and symplectic representations.
-/

public section

open Function
open scoped TensorProduct

namespace LinearMap

universe u v w

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w}

private noncomputable def contractTensorPairMultilinear (B : LinearMap.BilinForm R M)
    (i j : ι) (hij : i ≠ j) :
    MultilinearMap R (fun _ : ι => M) (⨂[R] _ : {a : ι // a ≠ i ∧ a ≠ j}, M) := by
  classical
  refine MultilinearMap.mk'
    (fun v => B (v i) (v j) •
      PiTensorProduct.tprod R (fun a : {a : ι // a ≠ i ∧ a ≠ j} => v a.val)) ?_ ?_
  · intro v a x y
    by_cases hai : a = i
    · subst a
      have hup (z : M) :
          (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v i z b.val) =
            (fun b => v b.val) :=
        update_comp_eq_of_forall_ne v z (fun b => b.property.1)
      simp only [update_self, update_of_ne hij.symm, hup, map_add, add_apply, add_smul]
    by_cases haj : a = j
    · subst a
      have hup (z : M) :
          (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v j z b.val) =
            (fun b => v b.val) :=
        update_comp_eq_of_forall_ne v z (fun b => b.property.2)
      simp only [update_self, update_of_ne hij, hup, map_add, add_smul]
    let a' : {b : ι // b ≠ i ∧ b ≠ j} := ⟨a, hai, haj⟩
    have hup (z : M) : (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v a z b.val) =
        update (fun b => v b.val) a' z := by
      exact update_comp_eq_of_injective v Subtype.val_injective a' z
    simp only [update_of_ne (Ne.symm hai), update_of_ne (Ne.symm haj), hup,
      (PiTensorProduct.tprod R).map_update_add, smul_add]
  · intro v a c x
    by_cases hai : a = i
    · subst a
      have hup (z : M) :
          (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v i z b.val) =
            (fun b => v b.val) :=
        update_comp_eq_of_forall_ne v z (fun b => b.property.1)
      simp only [update_self, update_of_ne hij.symm, hup, map_smul, smul_apply, smul_smul,
        smul_eq_mul]
    by_cases haj : a = j
    · subst a
      have hup (z : M) :
          (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v j z b.val) =
            (fun b => v b.val) :=
        update_comp_eq_of_forall_ne v z (fun b => b.property.2)
      simp only [update_self, update_of_ne hij, hup, map_smul, smul_smul, smul_eq_mul]
    let a' : {b : ι // b ≠ i ∧ b ≠ j} := ⟨a, hai, haj⟩
    have hup (z : M) : (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v a z b.val) =
        update (fun b => v b.val) a' z := by
      exact update_comp_eq_of_injective v Subtype.val_injective a' z
    simp only [update_of_ne (Ne.symm hai), update_of_ne (Ne.symm haj), hup,
      (PiTensorProduct.tprod R).map_update_smul, smul_comm (B (v i) (v j)) c]

/-- Contract two distinct slots against a bilinear form. The remaining factors keep their
original indices, restricted to the complement of the contracted pair. -/
noncomputable def contractTensorPair (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j) :
    (⨂[R] _ : ι, M) →ₗ[R] ⨂[R] _ : {a : ι // a ≠ i ∧ a ≠ j}, M :=
  PiTensorProduct.lift (contractTensorPairMultilinear B i j hij)

/-- On pure tensors, contraction pairs the selected factors and retains the others. -/
@[simp]
theorem contractTensorPair_tprod (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j) (v : ι → M) :
    B.contractTensorPair i j hij (PiTensorProduct.tprod R v) =
      B (v i) (v j) • PiTensorProduct.tprod R (fun a : {a : ι // a ≠ i ∧ a ≠ j} => v a.val) := by
  classical
  rw [contractTensorPair, PiTensorProduct.lift.tprod]
  rfl

/-- Contraction commutes with a diagonal linear map preserving the bilinear pairing. -/
theorem contractTensorPair_comp_map (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j)
    (f : M →ₗ[R] M) (hf : ∀ x y, B (f x) (f y) = B x y) :
    B.contractTensorPair i j hij ∘ₗ PiTensorProduct.map (fun _ : ι => f) =
      PiTensorProduct.map (fun _ : {a : ι // a ≠ i ∧ a ≠ j} => f) ∘ₗ
        B.contractTensorPair i j hij := by
  apply PiTensorProduct.ext
  ext v
  simp [hf]

/-- Renaming the slots renames a contracted pair and the complementary output slots. -/
theorem contractTensorPair_reindex (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j)
    {κ : Type*} (e : ι ≃ κ) (x : ⨂[R] _ : ι, M) :
    let e' : {a : ι // a ≠ i ∧ a ≠ j} ≃ {a : κ // a ≠ e i ∧ a ≠ e j} :=
      e.subtypeEquiv (fun a => by simp only [ne_eq, e.injective.eq_iff])
    B.contractTensorPair (e i) (e j) (e.injective.ne hij)
        (PiTensorProduct.reindex R (fun _ : ι => M) e x) =
      PiTensorProduct.reindex R (fun _ : {a : ι // a ≠ i ∧ a ≠ j} => M) e'
        (B.contractTensorPair i j hij x) := by
  dsimp only
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, PiTensorProduct.reindex_tprod, contractTensorPair_tprod]
    simp only [Equiv.subtypeEquiv]
    rw [e.symm_apply_apply i, e.symm_apply_apply j]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end LinearMap
