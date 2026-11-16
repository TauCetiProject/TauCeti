/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Upper-divisor sums of the Möbius function

For squarefree `m`, the Möbius function summed over the divisors of `m` that are multiples
of `l` vanishes unless `l = m`, when the sum is `μ l`.
-/

public section

open Finset Nat
open scoped ArithmeticFunction.Moebius

namespace ArithmeticFunction

/-- The Möbius sum over divisors of a squarefree number that are multiples of `l`. -/
theorem sum_moebius_upper (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) =
      if l = m then (μ l : ℤ) else 0 := by
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on'
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd) (by simp)).mpr
  intro m hm
  rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • if l = y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [ite_eq_left hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [ite_eq_left rfl, smul_eq_mul, ← isMultiplicative_moebius.map_mul_of_coprime, hmul]
      exact coprime_of_squarefree_mul (hmul.symm ▸ hm)
    · intro d _ hdl
      rw [ite_eq_right hdl.symm, smul_zero]
    · intro h
      exact False.elim (h (mem_divisors.mpr ⟨hl, hm.ne_zero⟩))
  · rw [ite_eq_right hl, sum_eq_zero]
    intro d hd
    rw [ite_eq_right, smul_zero]
    intro h
    exact hl (h ▸ dvd_of_mem_divisors hd)

end ArithmeticFunction
