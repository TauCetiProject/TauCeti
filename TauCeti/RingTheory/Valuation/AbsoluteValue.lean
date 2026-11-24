/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Absolute values from valuations

This file constructs an absolute value by composing a valuation with a monotone, zero-reflecting
monoid-with-zero homomorphism. The valuation must vanish only at zero, as it does on a division
ring when the value monoid is nontrivial. The construction also applies to valuations with trivial
support on general rings. When the codomain is linearly ordered, the resulting absolute value is
nonarchimedean.
-/

public section

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
