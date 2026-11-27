/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Absolute values from valuations

This file constructs an absolute value by composing a valuation with a monotone, zero-reflecting
monoid-with-zero homomorphism. The valuation must vanish only at zero, as it does on a division
ring when the value monoid is nontrivial. The construction also applies to valuations with trivial
support on general rings. When the codomain is linearly ordered, the resulting absolute value is
nonarchimedean.

In the other direction, a nonarchimedean real absolute value is a valuation with values in `ℝ≥0`
(`AbsoluteValue.toValuation`).
-/

public section

open scoped NNReal

namespace Valuation

section AbsoluteValue

variable {K S Γ₀ : Type*} [Ring K] [LinearOrderedCommMonoidWithZero Γ₀]
  [Semiring S] [PartialOrder S] [AddLeftMono S]
  (v : Valuation K Γ₀) (f : Γ₀ →*₀ S) (hf : Monotone f) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
  (hv_zero : ∀ x, v x = 0 ↔ x = 0)

/-- Compose a valuation that vanishes only at zero with a monotone, zero-reflecting
monoid-with-zero homomorphism to obtain an absolute value. -/
def toAbsoluteValue : AbsoluteValue K S :=
  -- Monotonicity and `f 0 = 0` make `f` nonnegative.
  have hf_nonneg (a : Γ₀) : 0 ≤ f a := (map_zero f).symm.trans_le (hf zero_le)
  AbsoluteValue.mk (f.comp v.toMonoidWithZeroHom) (fun x ↦ hf_nonneg (v x))
    (fun x ↦ (hf_zero (v x)).trans (hv_zero x))
    (fun x y ↦ by
      rcases v.map_add' x y with h | h
      · exact (hf h).trans (le_add_of_nonneg_right (hf_nonneg _))
      · exact (hf h).trans (le_add_of_nonneg_left (hf_nonneg _)))

/-- Evaluation of the absolute value obtained by composing a valuation with a monotone,
zero-reflecting monoid-with-zero homomorphism. -/
@[simp]
theorem toAbsoluteValue_apply (x : K) :
    v.toAbsoluteValue f hf hf_zero hv_zero x = f (v x) := (rfl)

/-- If one input has no larger absolute value than another, their sum has absolute value at most
that of the latter. The realization map need not reflect the order on valuations. -/
theorem toAbsoluteValue_add_le_right {x y : K}
    (h : v.toAbsoluteValue f hf hf_zero hv_zero x ≤ v.toAbsoluteValue f hf hf_zero hv_zero y) :
    v.toAbsoluteValue f hf hf_zero hv_zero (x + y) ≤ v.toAbsoluteValue f hf hf_zero hv_zero y := by
  simp only [toAbsoluteValue_apply] at h ⊢
  rcases v.map_add' x y with hx | hy
  · exact (hf hx).trans h
  · exact hf hy

end AbsoluteValue

section IsNonarchimedean

variable {K S Γ₀ : Type*} [Ring K] [LinearOrderedCommMonoidWithZero Γ₀]
  [Semiring S] [LinearOrder S] [AddLeftMono S]

/-- An absolute value obtained from a valuation through a monotone realization is
nonarchimedean. -/
theorem isNonarchimedean_toAbsoluteValue (v : Valuation K Γ₀) (f : Γ₀ →*₀ S) (hf : Monotone f)
    (hf_zero : ∀ a, f a = 0 ↔ a = 0) (hv_zero : ∀ x, v x = 0 ↔ x = 0) :
    IsNonarchimedean (v.toAbsoluteValue f hf hf_zero hv_zero) := by
  intro x y
  simpa only [toAbsoluteValue_apply, hf.map_max] using hf (v.map_add x y)

end IsNonarchimedean

end Valuation

namespace AbsoluteValue

/-- A nonarchimedean real absolute value, as a valuation with values in `ℝ≥0`. -/
def toValuation {R : Type*} [Ring R] [Nontrivial R] {w : AbsoluteValue R ℝ}
    (hw : IsNonarchimedean w) : Valuation R ℝ≥0 where
  toFun x := .mk (w x) (w.nonneg x)
  map_zero' := NNReal.eq w.map_zero
  map_one' := NNReal.eq w.map_one
  map_mul' x y := NNReal.eq (w.map_mul x y)
  map_add_le_max' x y := by exact_mod_cast hw x y

/-- The valuation attached to `w` takes the values of `w`. -/
@[simp]
theorem coe_toValuation_apply {R : Type*} [Ring R] [Nontrivial R] {w : AbsoluteValue R ℝ}
    (hw : IsNonarchimedean w) (x : R) : (w.toValuation hw x : ℝ) = w x :=
  NNReal.coe_mk _ _

end AbsoluteValue
