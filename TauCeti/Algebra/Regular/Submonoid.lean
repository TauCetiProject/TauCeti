/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The submonoid of regular elements

For a monoid `M`, `TauCeti.regularSubmonoid M` is the submonoid of regular elements (`IsRegular`),
those for which left and right multiplication are both injective. In a ring, `IsRegular` coincides
with membership in `nonZeroDivisors` (`R⁰`), whereas in a general semiring `regularSubmonoid` can
be strictly smaller than `nonZeroDivisors` and is the submonoid at which localization embeds the
base semiring injectively (`IsLocalization.injective_iff_isRegular`).
-/

public section

namespace TauCeti

/-- The submonoid of regular elements of a monoid: elements whose left and right multiplication
maps are injective. -/
def regularSubmonoid (M : Type*) [Monoid M] : Submonoid M where
  carrier := {a | IsRegular a}
  one_mem' := isRegular_one
  mul_mem' ha hb := ha.mul hb

@[simp]
theorem mem_regularSubmonoid {M : Type*} [Monoid M] {a : M} :
    a ∈ regularSubmonoid M ↔ IsRegular a :=
  Iff.rfl

theorem coe_regularSubmonoid (M : Type*) [Monoid M] :
    (regularSubmonoid M : Set M) = {a | IsRegular a} :=
  (rfl)

/-- Every regular element of a monoid with zero is a non-zero-divisor. -/
theorem regularSubmonoid_le_nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] :
    regularSubmonoid M₀ ≤ nonZeroDivisors M₀ :=
  fun _ => IsRegular.mem_nonZeroDivisors

/-- In a nontrivial cancellative monoid with zero (in particular, any domain semiring), the regular
elements are exactly the nonzero elements. -/
@[simp]
theorem coe_regularSubmonoid_of_isCancelMulZero (M₀ : Type*) [MonoidWithZero M₀]
    [IsCancelMulZero M₀] [Nontrivial M₀] :
    (regularSubmonoid M₀ : Set M₀) = {a | a ≠ 0} := by
  ext a
  exact isRegular_iff_ne_zero

/-- In a cancellative monoid with zero, the regular submonoid coincides with `nonZeroDivisors`. -/
theorem regularSubmonoid_eq_nonZeroDivisors_of_isCancelMulZero (M₀ : Type*) [MonoidWithZero M₀]
    [IsCancelMulZero M₀] :
    regularSubmonoid M₀ = nonZeroDivisors M₀ := by
  rcases subsingleton_or_nontrivial M₀ with h | h
  · ext a
    exact ⟨fun ha => ha.mem_nonZeroDivisors,
      fun _ => ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩⟩
  · ext a
    simp [isRegular_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]

/-- In a ring, multiplication is injective if and only if its kernel is zero, so the submonoid of
regular elements equals `nonZeroDivisors`. -/
@[simp]
theorem regularSubmonoid_eq_nonZeroDivisors (R : Type*) [Ring R] :
    regularSubmonoid R = nonZeroDivisors R := by
  ext a
  exact isRegular_iff_mem_nonZeroDivisors

end TauCeti
