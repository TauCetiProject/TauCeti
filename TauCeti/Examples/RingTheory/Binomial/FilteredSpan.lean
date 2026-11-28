/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Binomial.FilteredSpan
import Mathlib.Tactic.NoncommRing

/-!
# Checks of bounded integral binomial expansions

These examples use the bounded-span API through its public import. They cover an empty family,
an integer linear combination in two commuting variables, and its explicit quadratic expansion,
including a negative argument at `x = 0`, `y = 2`.
-/

namespace TauCeti

variable {R : Type*} [Ring R] [BinomialRing R]

-- Unit membership simplifies before singleton normalization unfolds the stage.
example (h : Fin 1 → R) (n : ℕ) : 1 ∈ ringChooseFilteredSpan h n := by
  simp

-- With no coordinates, integer binomials still lie in the integral span of one.
example (c : ℤ) (n : ℕ) :
    Ring.choose (c : R) n ∈ ringChooseFilteredSpan (Fin.elim0 : Fin 0 → R) n := by
  simpa using ringChoose_sum_zsmul_add_intCast_mem_ringChooseFilteredSpan
    (Fin.elim0 : Fin 0 → R) (fun i => Fin.elim0 i) (Fin.elim0 : Fin 0 → ℤ) c n

-- Both signs and the shift retain the degree-two bound.
example {x y : R} (hxy : Commute x y) :
    Ring.choose (2 * x - y + 1) 2 ∈ ringChooseFilteredSpan ![x, y] 2 := by
  have hcomm : ∀ i j : Fin 2, Commute (![x, y] i) (![x, y] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxy, hxy.symm, Commute.refl]
  simpa [Fin.sum_univ_two, zsmul_eq_mul, sub_eq_add_neg] using
    ringChoose_sum_zsmul_add_intCast_mem_ringChooseFilteredSpan ![x, y] hcomm ![2, -1] 1 2

-- The coefficients 4, -2, 1, and 3 multiply ordered binomial products of total degree at most two.
example {x y : R} (hxy : Commute x y) :
    Ring.choose (2 * x - y + 1) 2 =
      (4 : ℕ) • Ring.choose x 2 - (2 : ℕ) • (x * y) +
        Ring.choose y 2 + (3 : ℕ) • x := by
  have hchoose (a : R) : (2 : ℕ) • Ring.choose a 2 = a * (a - 1) := by
    simpa using Ring.add_one_nsmul_choose_add_one a 1
  let := BinomialRing.toHasUniqueDiv (R := R)
  apply nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  simp only [smul_add, smul_sub]
  rw [smul_comm (2 : ℕ) (4 : ℕ)]
  simp only [hchoose, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring [hxy.eq]

-- The quadratic expression above has value one at x = 0, y = 2.
example : Ring.choose (2 * (0 : R) - 2 + 1) 2 = 1 := by
  have harg : 2 * (0 : R) - 2 + 1 = -1 := by
    rw [mul_zero, zero_sub, ← one_add_one_eq_two]
    abel
  rw [harg]
  simp

end TauCeti
