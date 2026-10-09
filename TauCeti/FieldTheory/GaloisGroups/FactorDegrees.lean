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

It also records the two edge cases of that API. At a prime dividing the discriminant a factor can
repeat: Dedekind's cubic `X ^ 3 + X ^ 2 - 2 * X + 8` has discriminant `-2012 = -2² · 503` and
reduces to `X ^ 2 * (X + 1)` modulo `2`, with factor degrees `{1, 1, 1}`. By
`Polynomial.count_one_factorDegrees_le` no reduction modulo `2` at a prime not dividing the
discriminant has three linear factors. When `p` divides the leading coefficient the degree drops:
`2 * X ^ 2 + X + 1` has the single factor degree `1` modulo `2`.

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
* `Polynomial.discr_X_pow_three_add_X_sq_sub_two_mul_X_add_eight`,
  `Polynomial.factorDegrees_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_two`,
  `Polynomial.not_squarefree_map_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_zmod_two`:
  Dedekind's cubic has a repeated factor modulo the prime `2` dividing its discriminant.
* `Polynomial.factorDegrees_two_mul_X_sq_add_X_add_one_two`: a non-monic polynomial whose degree
  drops modulo `2`.

## References

* D. A. Marcus, *Number Fields*, 2nd edition, Springer 2018, Chapter 4, where the factorization
  of `f mod p` is matched with the splitting of `p`.
* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Chapter I, §8.
* R. Dedekind, *Über den Zusammenhang zwischen der Theorie der Ideale und der Theorie der höheren
  Congruenzen*, Abh. Kgl. Ges. Wiss. Göttingen 23 (1878), where the cubic
  `X ^ 3 + X ^ 2 - 2 * X + 8` appears.
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
  have hf : (X ^ 5 - X - 1 : (ZMod 5)[X]) = X ^ 5 + C (-1) * X + C (-1) := by
    simp only [map_neg, C_1]
    ring
  rw [hf]
  exact irreducible_X_pow_five_add_C_mul_X_add_C (by decide) (by decide)

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

/-! ### Edge cases: a repeated factor and a degree drop -/

/-- The discriminant of Dedekind's cubic `X ^ 3 + X ^ 2 - 2 * X + 8` is `-2012 = -2² · 503`. -/
theorem _root_.Polynomial.discr_X_pow_three_add_X_sq_sub_two_mul_X_add_eight :
    (X ^ 3 + X ^ 2 - 2 * X + 8 : ℤ[X]).discr = -2012 := by
  rw [discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_ofNat_mul, coeff_ofNat_zero,
    coeff_ofNat_succ]
  norm_num

private theorem map_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_zmod_two :
    (X ^ 3 + X ^ 2 - 2 * X + 8 : ℤ[X]).map (Int.castRingHom (ZMod 2)) =
      ({X, X, X + 1} : Multiset (ZMod 2)[X]).prod := by
  simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_ofNat]
  linear_combination (-X + 4 : (ZMod 2)[X]) * (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)

/-- Modulo `2`, Dedekind's cubic reduces to `X ^ 2 * (X + 1)`, so its factor degrees are
`{1, 1, 1}` with the linear factor `X` counted twice. The prime `2` divides the discriminant, by
`Polynomial.discr_X_pow_three_add_X_sq_sub_two_mul_X_add_eight`. -/
theorem _root_.Polynomial.factorDegrees_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_two :
    (X ^ 3 + X ^ 2 - 2 * X + 8 : ℤ[X]).factorDegrees 2 = {1, 1, 1} := by
  have hirr : ∀ q ∈ ({X, X, X + 1} : Multiset (ZMod 2)[X]), Irreducible q := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    rintro q (rfl | rfl | rfl)
    exacts [irreducible_X, irreducible_X, irreducible_of_degree_eq_one (degree_X_add_C 1)]
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hirr
    map_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_zmod_two]
  simp

/-- The reduction of Dedekind's cubic modulo `2` is not squarefree: `X ^ 2` divides it. -/
theorem _root_.Polynomial.not_squarefree_map_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_zmod_two :
    ¬ Squarefree ((X ^ 3 + X ^ 2 - 2 * X + 8 : ℤ[X]).map (Int.castRingHom (ZMod 2))) := by
  rw [map_X_pow_three_add_X_sq_sub_two_mul_X_add_eight_zmod_two]
  intro h
  exact not_isUnit_X (h X ⟨X + 1, by simp [Multiset.insert_eq_cons, mul_assoc]⟩)

/-- The non-monic `2 * X ^ 2 + X + 1` reduces to the linear `X + 1` modulo `2`, so its only factor
degree is `1`: when `p` divides the leading coefficient, the factor degrees sum to less than the
degree. -/
theorem _root_.Polynomial.factorDegrees_two_mul_X_sq_add_X_add_one_two :
    (2 * X ^ 2 + X + 1 : ℤ[X]).factorDegrees 2 = {1} := by
  rw [factorDegrees_eq_singleton_iff]
  have hmap : (2 * X ^ 2 + X + 1 : ℤ[X]).map (Int.castRingHom (ZMod 2)) = X + 1 := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, Polynomial.map_one]
    linear_combination (X ^ 2 : (ZMod 2)[X]) * (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
  rw [hmap]
  exact ⟨irreducible_of_degree_eq_one (by compute_degree!), by compute_degree!⟩

end TauCeti
