/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import TauCeti.Algebra.Order.Antidiag.Moments
import Mathlib.Logic.Equiv.Prod

/-!
# First moments of monomials of fixed degree in several blocks

A monomial of prescribed degree in each block is a tuple of elements of finitely supported
antidiagonals. For any one variable, its mean exponent is the degree of its block divided
by the number of variables in that block. The result below clears the denominator.
-/

public section

open Finset

/-- The sum of the exponents at one coordinate over a product of fixed-degree antidiagonals,
multiplied by the size of the selected block. -/
theorem Finset.card_mul_sum_pi_finsuppAntidiag_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ j, DecidableEq (κ j)] (s : ∀ j, Finset (κ j)) (n : ι → ℕ)
    (j : ι) {i : κ j} (hi : i ∈ s j) :
    (s j).card * (∑ e : (∀ l, ↥((s l).finsuppAntidiag (n l))), (e j).val i) =
      n j * Fintype.card (∀ l, ↥((s l).finsuppAntidiag (n l))) := by
  classical
  let e := Equiv.piSplitAt j (fun l ↦ ↥((s l).finsuppAntidiag (n l)))
  rw [Fintype.card_congr e, Fintype.card_prod]
  have h := Fintype.sum_equiv e (fun a ↦ (a j).val i) (fun a ↦ a.1.val i) (fun _ ↦ rfl)
  rw [Fintype.sum_prod_type] at h
  simp only [sum_const, smul_eq_mul, ← mul_sum] at h
  rw [h, mul_left_comm, Finset.univ_eq_attach, Finset.sum_attach ((s j).finsuppAntidiag (n j))
    (fun v ↦ v i), card_mul_sum_finsuppAntidiag_apply hi]
  simp only [Fintype.card_coe, card_univ]
  ac_rfl
