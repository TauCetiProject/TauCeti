/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.Parameters
import Mathlib.Tactic.NormNum
import TauCeti.Algebra.AddCircle

/-!
# Examples of hypergeometric parameter pairs

Concrete parameter pairs, with classes in `ℚ/ℤ` written through their representatives in
`(0, 1]`:

* `α = {1/2}`, `β = {1}` (the class of `0`) is a pair of degree `1`, and its `β` displays the
  class of `0` as `1`, not `0`.
* `α = {1/4, 3/4}`, `β = {1/2, 1}` has common denominator `4`, the lcm of the additive orders
  `4, 4, 2, 1`. Both the shift by `1/2` and the negation map it to itself.
-/

public section

open TauCeti.Hypergeometric

namespace TauCeti.Hypergeometric.Examples

/-- The pair `α = {1/2}`, `β = {1}`. -/
noncomputable def half : Parameters where
  α := {((1 / 2 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.mem_singleton]
    rintro _ rfl _ rfl
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (a := 0) (by norm_num) (by norm_num)).not.2
        (by norm_num)

example : half.degree = 1 := by
  rw [← Parameters.card_α]
  rfl

-- The class `1` of `β` is the class of `0`, displayed as `1` by `rep` and as `0` by `rep0`.
example : half.β = {0} ∧ rep 0 = 1 ∧ rep0 0 = 0 :=
  ⟨by simp [half, AddCircle.coe_period], rep_zero, rep0_zero⟩

/-- The pair `α = {1/4, 3/4}`, `β = {1/2, 1}`. -/
noncomputable def quarter : Parameters where
  α := {((1 / 4 : ℚ) : AddCircle (1 : ℚ)), ((3 / 4 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 / 2 : ℚ) : AddCircle (1 : ℚ)), ((1 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton]
    rintro _ (rfl | rfl) _ (rfl | rfl) <;>
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (a := 0) (by norm_num) (by norm_num)).not.2
          (by norm_num)

example : quarter.degree = 2 := by
  rw [← Parameters.card_α]
  rfl

/-- The common denominator of `quarter` is `4`. -/
theorem denominator_quarter : quarter.denominator = 4 := by
  refine Nat.dvd_antisymm (quarter.denominator_dvd_iff.2 ?_) ?_
  · simp only [quarter, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
      Multiset.mem_cons, Multiset.mem_singleton]
    rintro _ (rfl | rfl | rfl | rfl) <;>
      rw [← AddCircle.coe_nsmul, nsmul_eq_mul, AddCircle.coe_eq_zero_iff_den_eq_one] <;> norm_num
  · have h := quarter.addOrderOf_dvd_denominator (a := ((1 / 4 : ℚ) : AddCircle (1 : ℚ)))
      (by simp [quarter])
    rwa [show (1 / 4 : ℚ) = 1 / (4 : ℕ) by norm_num,
      AddCircle.addOrderOf_period_div (by norm_num)] at h

-- The shift by `1/2` exchanges `1/4 ↔ 3/4` and `1/2 ↔ 1`.
example : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) +ᵥ quarter = quarter := by
  ext1
  · simp only [Parameters.vadd_α, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_add]
    rw [show (1 / 2 + 1 / 4 : ℚ) = 3 / 4 + ((0 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast,
      show (1 / 2 + 3 / 4 : ℚ) = 1 / 4 + ((1 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast]
    exact Multiset.pair_comm _ _
  · simp only [Parameters.vadd_β, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_add]
    rw [show (1 / 2 + 1 / 2 : ℚ) = 1 + ((0 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast,
      show (1 / 2 + 1 : ℚ) = 1 / 2 + ((1 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast]
    exact Multiset.pair_comm _ _

-- The negation also exchanges `1/4 ↔ 3/4`, and fixes `1/2` and `1`.
example : -quarter = quarter := by
  ext1
  · simp only [Parameters.neg_α, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_neg]
    rw [show (-(1 / 4) : ℚ) = 3 / 4 + ((-1 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast,
      show (-(3 / 4) : ℚ) = 1 / 4 + ((-1 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast]
    exact Multiset.pair_comm _ _
  · simp only [Parameters.neg_β, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_neg]
    rw [show (-(1 / 2) : ℚ) = 1 / 2 + ((-1 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast,
      show (-1 : ℚ) = 1 + ((-2 : ℤ) : ℚ) by norm_num,
      AddCircle.coe_add_intCast]

end TauCeti.Hypergeometric.Examples
