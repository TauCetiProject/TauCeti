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
support on general rings.
-/

public section

namespace Valuation

section AbsoluteValue

variable {K S Γ₀ : Type*} [Ring K] [LinearOrderedCommMonoidWithZero Γ₀]
  [Semiring S] [PartialOrder S] [addLeftMono : AddLeftMono S]

/-- Compose a valuation that vanishes only at zero with a monotone, zero-reflecting
monoid-with-zero homomorphism to obtain an absolute value. -/
def toAbsoluteValue (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    (hv_zero : ∀ x, v x = 0 ↔ x = 0) :
    AbsoluteValue K S :=
  AbsoluteValue.mk (f.comp v.toMonoidWithZeroHom)
    (fun x ↦ by rw [← map_zero f]; exact hf zero_le)
    (fun x ↦ (hf_zero (v x)).trans (hv_zero x))
    (fun x y ↦ by
      refine (hf (v.map_add x y)).trans ?_
      rcases le_total (v x) (v y) with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left <| by rw [← map_zero f]; exact hf zero_le
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right <| by rw [← map_zero f]; exact hf zero_le)

include addLeftMono in
/-- Evaluation of the absolute value obtained by composing a valuation with a monotone,
zero-reflecting monoid-with-zero homomorphism. -/
@[simp]
theorem toAbsoluteValue_apply (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    (hv_zero : ∀ x, v x = 0 ↔ x = 0) (x : K) :
    v.toAbsoluteValue f hf hf_zero hv_zero x = f (v x) := (rfl)

include addLeftMono in
/-- If one input has no larger absolute value than another, their sum has absolute value at most
that of the latter. The realization map need not reflect the order on valuations. -/
theorem toAbsoluteValue_add_le_right (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    (hv_zero : ∀ x, v x = 0 ↔ x = 0)
    {x y : K} (h : v.toAbsoluteValue f hf hf_zero hv_zero x ≤
      v.toAbsoluteValue f hf hf_zero hv_zero y) :
    v.toAbsoluteValue f hf hf_zero hv_zero (x + y) ≤
      v.toAbsoluteValue f hf hf_zero hv_zero y := by
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
theorem isNonarchimedean_toAbsoluteValue (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    (hv_zero : ∀ x, v x = 0 ↔ x = 0) :
    IsNonarchimedean (v.toAbsoluteValue f hf hf_zero hv_zero) := by
  intro x y
  simpa only [toAbsoluteValue_apply, Monotone.map_max hf] using hf (v.map_add x y)

end IsNonarchimedean

end Valuation
