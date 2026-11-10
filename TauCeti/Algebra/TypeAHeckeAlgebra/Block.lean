/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Disjoint blocks embed in the Hecke tower

The disjoint block map places two Hecke stages on consecutive blocks of strands. This file
proves that it is injective over every commutative coefficient ring and at every unit parameter.
Thus the two coefficient algebras embed as their tensor product, including at singular
parameters, as required for induction from disjoint blocks.

The proof reuses `cosetEquiv` and `shift_cosetRep` from the coset-basis construction. The coset
representatives for the second block become the representatives with indices shifted by the
size of the first block, so uniqueness of the larger stage's coset coordinates recovers every
tensor coefficient.
-/

public section

open scoped TensorProduct

namespace TauCeti.InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

private theorem blockIncl_zero_injective (a : ℕ) :
    Function.Injective (blockIncl R q a 0) := by
  have hinv (z : stage R q a ⊗[R] stage R q 0) :
      blockIncl R q a 0 z ⊗ₜ[R] (1 : stage R q 0) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hy0 := (stage_eq_bot_of_le_one (R := R) (q := q) (n := 0) (by omega)).le y.2
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hy0
      have hy : y = algebraMap R _ r := Subtype.ext hr.symm
      subst y
      have hb : blockIncl R q a 0 (x ⊗ₜ[R] algebraMap R _ r) = r • x := by
        apply Subtype.ext
        exact (coe_blockIncl_tmul x (algebraMap R _ r)).trans (by
          simp [Algebra.smul_def, Algebra.commutes])
      rw [hb, TensorProduct.smul_tmul]
      simp [Algebra.algebraMap_eq_smul_one]
    | add z z' hz hz' => simp [map_add, TensorProduct.add_tmul, hz, hz']
  exact Function.LeftInverse.injective
    (g := fun x : stage R q a ↦ x ⊗ₜ[R] (1 : stage R q 0)) hinv

private theorem cosetEquiv_symm_blockIncl_single (a b : ℕ)
    (x : stage R q a) (y : stage R q b) (j : Fin (b + 1)) :
    (cosetEquiv R q (a + b)).symm
      (blockIncl R q a (b + 1) (x ⊗ₜ[R] cosetEquiv R q b (Pi.single j y))) =
      Pi.single ⟨a + j, by omega⟩ (blockIncl R q a b (x ⊗ₜ[R] y)) := by
  classical
  rw [← cosetEquiv_symm_inclusion_mul_cosetRep
    (n := a + b) ⟨a + j, by omega⟩ (blockIncl R q a b (x ⊗ₜ[R] y))]
  congr 1
  apply Subtype.ext
  simp [coe_blockIncl_tmul, coe_cosetEquiv_apply, shift_cosetRep,
    Nat.add_comm, Pi.single_apply, apply_ite, mul_assoc]

/-- The disjoint block map is an embedding, over every commutative ring and at every unit
parameter. No semisimplicity or invertibility of a quantum integer is required. -/
theorem blockIncl_injective (a b : ℕ) : Function.Injective (blockIncl R q a b) := by
  classical
  induction b with
  | zero => exact blockIncl_zero_injective a
  | succ b ih =>
    let e : (stage R q a ⊗[R] stage R q (b + 1)) ≃ₗ[R]
        (Fin (b + 1) → stage R q a ⊗[R] stage R q b) :=
      (TensorProduct.congr (LinearEquiv.refl R _) (cosetEquiv R q b).symm).trans
        (TensorProduct.piRight R R (stage R q a) fun _ : Fin (b + 1) ↦ stage R q b)
    let idx : Fin (b + 1) → Fin (a + b + 1) := fun j ↦ ⟨a + j, by omega⟩
    have hcoord (z : stage R q a ⊗[R] stage R q (b + 1)) (j : Fin (b + 1)) :
        (cosetEquiv R q (a + b)).symm (blockIncl R q a (b + 1) z) (idx j) =
          blockIncl R q a b (e z j) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        let c := (cosetEquiv R q b).symm y
        have hy : y = ∑ i, cosetEquiv R q b (Pi.single i (c i)) := by
          calc
            y = cosetEquiv R q b c := ((cosetEquiv R q b).apply_symm_apply y).symm
            _ = cosetEquiv R q b (∑ i, Pi.single i (c i)) := by
              rw [Finset.univ_sum_single]
            _ = ∑ i, cosetEquiv R q b (Pi.single i (c i)) :=
              map_sum (cosetEquiv R q b).toLinearMap _ _
        conv_lhs => rw [hy, TensorProduct.tmul_sum, map_sum, map_sum]
        simp only [Finset.sum_apply, cosetEquiv_symm_blockIncl_single]
        simp [e, c, idx, Pi.single_apply, Fin.mk.injEq, Fin.val_inj]
      | add z z' hz hz' => simp [map_add, hz, hz']
    intro z z' h
    apply e.injective
    funext j
    apply ih
    rw [← hcoord, ← hcoord, h]

end TauCeti.InfiniteTypeAHeckeAlgebra
