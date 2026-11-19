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

/-- Two rationals in `(0, 1]` with different values give different classes in `ℚ/ℤ`. -/
private theorem coe_ne_coe {q r : ℚ} (hq : q ∈ Set.Ioc (0 : ℚ) 1) (hr : r ∈ Set.Ioc (0 : ℚ) 1)
    (h : q ≠ r) : (q : AddCircle (1 : ℚ)) ≠ r := fun e ↦
  h (by rw [← rep_coe_of_mem hq, ← rep_coe_of_mem hr, e])

/-- Two rationals differing by an integer give the same class in `ℚ/ℤ`. -/
private theorem coe_eq_coe {q r : ℚ} (m : ℤ) (h : q - r = m) :
    (q : AddCircle (1 : ℚ)) = r :=
  sub_eq_zero.1 <| by
    rw [← AddCircle.coe_sub, h]
    exact (AddCircle.coe_eq_zero_iff 1).2 ⟨m, by simp⟩

/-- A multiple of a class vanishes once the corresponding multiple of a representative is an
integer. -/
private theorem nsmul_coe_eq_zero {n : ℕ} {q : ℚ} (h : (n * q).den = 1) :
    n • (q : AddCircle (1 : ℚ)) = 0 := by
  rwa [← AddCircle.coe_nsmul, nsmul_eq_mul, AddCircle.coe_eq_zero_iff_den_eq_one]

/-- The pair `α = {1/2}`, `β = {1}`. -/
noncomputable def half : Parameters where
  α := {((1 / 2 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.mem_singleton]
    rintro _ rfl _ rfl
    exact coe_ne_coe (by norm_num) (by norm_num) (by norm_num)

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
      exact coe_ne_coe (by norm_num) (by norm_num) (by norm_num)

example : quarter.degree = 2 := by
  rw [← Parameters.card_α]
  rfl

/-- The common denominator of `quarter` is `4`. -/
theorem denominator_quarter : quarter.denominator = 4 := by
  refine Nat.dvd_antisymm (quarter.denominator_dvd_iff.2 ?_) ?_
  · simp only [quarter, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
      Multiset.mem_cons, Multiset.mem_singleton]
    rintro _ (rfl | rfl | rfl | rfl) <;> exact nsmul_coe_eq_zero (by norm_num)
  · have h := quarter.addOrderOf_dvd_denominator (a := ((1 / 4 : ℚ) : AddCircle (1 : ℚ)))
      (by simp [quarter])
    rwa [show (1 / 4 : ℚ) = 1 / (4 : ℕ) by norm_num,
      AddCircle.addOrderOf_period_div (by norm_num)] at h

-- The shift by `1/2` exchanges `1/4 ↔ 3/4` and `1/2 ↔ 1`.
example : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) +ᵥ quarter = quarter := by
  ext1
  · simp only [Parameters.vadd_α, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_add]
    rw [coe_eq_coe 0 (q := 1 / 2 + 1 / 4) (r := 3 / 4) (by norm_num),
      coe_eq_coe 1 (q := 1 / 2 + 3 / 4) (r := 1 / 4) (by norm_num)]
    exact Multiset.pair_comm _ _
  · simp only [Parameters.vadd_β, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_add]
    rw [coe_eq_coe 0 (q := 1 / 2 + 1 / 2) (r := 1) (by norm_num),
      coe_eq_coe 1 (q := 1 / 2 + 1) (r := 1 / 2) (by norm_num)]
    exact Multiset.pair_comm _ _

-- The negation also exchanges `1/4 ↔ 3/4`, and fixes `1/2` and `1`.
example : -quarter = quarter := by
  ext1
  · simp only [Parameters.neg_α, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_neg]
    rw [coe_eq_coe (-1) (q := -(1 / 4)) (r := 3 / 4) (by norm_num),
      coe_eq_coe (-1) (q := -(3 / 4)) (r := 1 / 4) (by norm_num)]
    exact Multiset.pair_comm _ _
  · simp only [Parameters.neg_β, quarter, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, ← AddCircle.coe_neg]
    rw [coe_eq_coe (-1) (q := -(1 / 2)) (r := 1 / 2) (by norm_num),
      coe_eq_coe (-2) (q := -1) (r := 1) (by norm_num)]

end TauCeti.Hypergeometric.Examples
