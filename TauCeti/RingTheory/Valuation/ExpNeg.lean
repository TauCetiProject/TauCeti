/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Integer additive valuations as `ℤᵐ⁰`-valued valuations

An additive valuation `v : R → WithTop ℤ`, such as the order of vanishing of a meromorphic
function, is the same data as a multiplicative valuation `R → ℤᵐ⁰`: send a finite value `n` to
`exp (-n)` and `⊤` to `0`. Mathlib's `AddValuation.toValuation` lands in
`Multiplicative (WithTop ℤ)ᵒᵈ` instead, which is not the value monoid `ℤᵐ⁰` of normalized discrete
valuations. This file makes the translation to `ℤᵐ⁰` explicit.

## Main definitions

* `WithTop.expNeg`: the order-reversing translation `⊤ ↦ 0`, `n ↦ exp (-n)` from `WithTop ℤ` to
  `ℤᵐ⁰`.
* `AddValuation.expNeg`: the valuation `r ↦ exp (-v r)` of an additive valuation
  `v : R → WithTop ℤ`.
-/

public section

open scoped WithZero

namespace WithTop

/-- The order-reversing translation `⊤ ↦ 0`, `n ↦ exp (-n)` from additive to multiplicative
values. -/
noncomputable def expNeg (a : WithTop ℤ) : ℤᵐ⁰ :=
  if a = ⊤ then 0 else WithZero.exp (-a.untopD 0)

@[simp]
theorem expNeg_top : expNeg ⊤ = 0 := by simp [expNeg]

@[simp]
theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := by
  simp [expNeg]

@[simp]
theorem expNeg_zero : expNeg 0 = 1 := by
  rw [← WithTop.coe_zero, expNeg_coe, neg_zero, WithZero.exp_zero]

theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    simp [← WithTop.coe_add, ← WithZero.exp_add, add_comm]

theorem expNeg_antitone : Antitone expNeg := by
  intro a b hab
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    induction a using WithTop.recTopCoe with
    | top => simp at hab
    | coe m => simpa using WithTop.coe_le_coe.mp hab

end WithTop

namespace AddValuation

variable {R : Type*} [Ring R]

/-- The multiplicative valuation `r ↦ exp (-v r)` of an additive valuation `v : R → WithTop ℤ`,
with values in `ℤᵐ⁰`. -/
noncomputable def expNeg (v : AddValuation R (WithTop ℤ)) : Valuation R ℤᵐ⁰ where
  toFun r := (v r).expNeg
  map_zero' := by rw [AddValuation.map_zero, WithTop.expNeg_top]
  map_one' := by rw [AddValuation.map_one, WithTop.expNeg_zero]
  map_mul' r s := by rw [AddValuation.map_mul, WithTop.expNeg_add]
  map_add_le_max' r s := by
    rw [← WithTop.expNeg_antitone.map_min]
    exact WithTop.expNeg_antitone (AddValuation.map_add v r s)

@[simp]
theorem expNeg_apply (v : AddValuation R (WithTop ℤ)) (r : R) : v.expNeg r = (v r).expNeg :=
  (rfl)

end AddValuation
