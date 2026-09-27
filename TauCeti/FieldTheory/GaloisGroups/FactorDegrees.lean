/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.FactorDegrees
import TauCeti.Algebra.Polynomial.SpecificDegree

import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Degrees of factors modulo a prime

This module works out `Polynomial.factorDegrees` explicitly for `X ^ 5 - X - 1`, whose reduction
splits as a cubic times a quadratic modulo `2` and stays irreducible modulo `5`. The generic
polynomial carrier and API live in `TauCeti/RingTheory/Polynomial/FactorDegrees.lean`.

## Main declarations

* `Polynomial.irreducible_X_sq_add_X_add_one_zmod_two`,
  `Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two`: the two irreducibility facts
  over `ZMod 2` that the modulo `2` example rests on.
* `Polynomial.irreducible_X_pow_five_sub_X_sub_one_zmod_five`: the irreducibility fact over
  `ZMod 5` that the modulo `5` example rests on.
* `Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_two`: the worked example
  `factorDegrees (X ^ 5 - X - 1) 2 = {3, 2}`.
* `Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_five`: the worked example
  `factorDegrees (X ^ 5 - X - 1) 5 = {5}`.

## References

* D. A. Marcus, *Number Fields*, 2nd edition, Springer 2018, Chapter 4, where the factorization
  of `f mod p` is matched with the splitting of `p`.
* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Chapter I, §8.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-! ### The factorization of `X ^ 5 - X - 1` modulo `2` and `5` -/

private theorem natDegree_X_pow_three_add_X_sq_add_one :
    (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!

private theorem natDegree_X_sq_add_X_add_one :
    (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!

/-- `X ^ 2 + X + 1` is irreducible over `ZMod 2`: it is quadratic and has no root there. -/
theorem _root_.Polynomial.irreducible_X_sq_add_X_add_one_zmod_two :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_sq_add_X_add_one]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- `X ^ 3 + X ^ 2 + 1` is irreducible over `ZMod 2`: it is cubic and has no root there. -/
theorem _root_.Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two :
    Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_three_add_X_sq_add_one]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- The polynomial `X ^ 5 - X - 1` has factor degrees `3` and `2` modulo `2`: its reduction is
the product of the irreducibles `X ^ 3 + X ^ 2 + 1` and `X ^ 2 + X + 1`. -/
theorem _root_.Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_two :
    (X ^ 5 - X - 1 : ℤ[X]).factorDegrees 2 = {3, 2} := by
  have hirr : ∀ q ∈ ({X ^ 3 + X ^ 2 + 1, X ^ 2 + X + 1} : Multiset (ZMod 2)[X]),
      Irreducible q := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact Polynomial.irreducible_X_pow_three_add_X_sq_add_one_zmod_two
    · rw [Multiset.mem_singleton.mp hq]
      exact Polynomial.irreducible_X_sq_add_X_add_one_zmod_two
  have hmap : (X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 2)) =
      ({X ^ 3 + X ^ 2 + 1, X ^ 2 + X + 1} : Multiset (ZMod 2)[X]).prod := by
    rw [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    linear_combination (-(X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : (ZMod 2)[X]) *
      (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hirr hmap]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    natDegree_X_pow_three_add_X_sq_add_one, natDegree_X_sq_add_X_add_one]

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- `X ^ 5 - X - 1` is irreducible over `ZMod 5`. -/
theorem _root_.Polynomial.irreducible_X_pow_five_sub_X_sub_one_zmod_five :
    Irreducible (X ^ 5 - X - 1 : (ZMod 5)[X]) := by
  have hmonic : Monic (X ^ 5 - X - 1 : (ZMod 5)[X]) := by
    rw [sub_sub]
    apply Polynomial.monic_X_pow_sub
    compute_degree!
  have hpdeg : (X ^ 5 - X - 1 : (ZMod 5)[X]).natDegree = 5 := by
    rw [sub_sub]
    compute_degree!
  have hpone : (X ^ 5 - X - 1 : (ZMod 5)[X]) ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hpdeg
    omega
  rw [hmonic.irreducible_iff_lt_natDegree_lt hpone]
  intro q hq hdeg hdvd
  have hdeg' : q.natDegree = 1 ∨ q.natDegree = 2 := by
    rw [hpdeg] at hdeg
    simp only [Finset.mem_Ioc] at hdeg
    norm_num at hdeg
    omega
  rcases hdeg' with hdeg' | hdeg'
  · rw [hq.eq_X_add_C hdeg'] at hdvd
    rw [← sub_neg_eq_add, ← Polynomial.C_neg, Polynomial.dvd_iff_isRoot,
      Polynomial.IsRoot.def] at hdvd
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hdvd
    rw [ZMod.pow_card] at hdvd
    norm_num at hdvd
  · let a := q.coeff 1
    let b := q.coeff 0
    -- Put a hypothetical monic quadratic factor in coefficient form.
    have hqeq : q = X ^ 2 + C a * X + C b := by
      rw [Polynomial.eq_quadratic_of_degree_le_two
        (Polynomial.degree_le_of_natDegree_le hdeg'.le)]
      have hc : q.coeff 2 = 1 := by simpa [hdeg'] using hq.coeff_natDegree
      rw [hc]
      simp [a, b]
    have hdvd' : X ^ 2 + C a * X + C b ∣
        X ^ 5 + C (-1 : ZMod 5) * X + C (-1 : ZMod 5) := by
      simpa only [hqeq, C_neg, C_1, neg_one_mul, sub_eq_add_neg] using hdvd
    rw [X_sq_add_C_mul_X_add_C_dvd_X_pow_five_add_iff] at hdvd'
    -- None of the 25 coefficient pairs in `ZMod 5` satisfies both equations.
    have hno : ∀ a b : ZMod 5,
        ¬ (a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + -1 = 0 ∧
          a ^ 3 * b - 2 * a * b ^ 2 + -1 = 0) := by decide
    exact hno a b hdvd'

/-- The polynomial `X ^ 5 - X - 1` is irreducible modulo `5`, so its sole factor degree is `5`. -/
theorem _root_.Polynomial.factorDegrees_X_pow_five_sub_X_sub_one_five :
    (X ^ 5 - X - 1 : ℤ[X]).factorDegrees 5 = {5} := by
  rw [Polynomial.factorDegrees_eq_singleton_iff]
  have hmap : (X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 5)) =
      (X ^ 5 - X - 1 : (ZMod 5)[X]) := by norm_num
  rw [hmap]
  constructor
  · exact Polynomial.irreducible_X_pow_five_sub_X_sub_one_zmod_five
  · rw [sub_sub]
    compute_degree!

end TauCeti
