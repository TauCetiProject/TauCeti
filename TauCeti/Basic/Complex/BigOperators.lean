/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators

/-!
# Finite sums of complex numbers

## Weighted sums of squared absolute values

A finitely supported family of complex numbers `f` and real weights `w` give the real sum
`∑ₛ |f s|² w s`, which is the weighted Hermitian sum `∑ₛ conj (f s) * w s * f s`
(`Finsupp.ofReal_sum_normSq_mul`). For nonnegative weights this sum is nonnegative
(`Finsupp.sum_normSq_mul_nonneg`) and vanishes exactly when `f` vanishes at every index of nonzero
weight (`Finsupp.sum_normSq_mul_eq_zero_iff`).

## Real parts of squared scaled sums

For any real scalar `c` and finite family `f : ι → ℂ`, expanding the square of
`(c : ℂ) * ∑ i ∈ s, f i` and pulling out the real factor `c ^ 2` expresses its real part as
`c ^ 2 * (∑ p ∈ s ×ˢ s, f p.1 * f p.2).re` (`Complex.re_ofReal_mul_sum_sq`).
-/

public section

open ComplexConjugate

namespace Finsupp

/-- The real sum `∑ₛ |f s|² w s`, viewed as a complex number, is the weighted Hermitian sum
`∑ₛ conj (f s) * (w s * f s)`. -/
theorem ofReal_sum_normSq_mul {α : Type*} (f : α →₀ ℂ) (w : α → ℝ) :
    (((f.sum fun s z ↦ Complex.normSq z * w s : ℝ)) : ℂ) =
      f.sum fun s z ↦ conj z * ((w s : ℂ) * f s) := by
  rw [Finsupp.sum, Finsupp.sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  ring

/-- A real sum `∑ₛ |f s|² w s` with nonnegative weights is nonnegative. -/
theorem sum_normSq_mul_nonneg {α : Type*} (f : α →₀ ℂ) {w : α → ℝ} (hw : ∀ s, 0 ≤ w s) :
    0 ≤ f.sum fun s z ↦ Complex.normSq z * w s :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (Complex.normSq_nonneg _) (hw s)

/-- A real sum `∑ₛ |f s|² w s` with nonnegative weights vanishes exactly when `f` vanishes at every
index of nonzero weight. -/
theorem sum_normSq_mul_eq_zero_iff {α : Type*} (f : α →₀ ℂ) {w : α → ℝ} (hw : ∀ s, 0 ≤ w s) :
    (f.sum fun s z ↦ Complex.normSq z * w s) = 0 ↔ ∀ s, w s ≠ 0 → f s = 0 := by
  rw [Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun s _ ↦
    mul_nonneg (Complex.normSq_nonneg _) (hw s)]
  refine ⟨fun h s hs ↦ ?_, fun h s _ ↦ ?_⟩
  · by_contra hf
    exact hf (Complex.normSq_eq_zero.mp
      ((mul_eq_zero.mp (h s (Finsupp.mem_support_iff.mpr hf))).resolve_right hs))
  · by_cases hs : w s = 0
    · simp [hs]
    · simp [h s hs]

end Finsupp

namespace Complex

/-- The real part of the square of a real-scaled complex finite sum `(c : ℂ) * ∑ i ∈ s, f i`
equals `c ^ 2 * (∑ p ∈ s ×ˢ s, f p.1 * f p.2).re`. -/
theorem re_ofReal_mul_sum_sq {ι : Type*} (s : Finset ι) (c : ℝ) (f : ι → ℂ) :
    (((c : ℂ) * ∑ i ∈ s, f i) ^ 2).re = c ^ 2 * (∑ p ∈ s ×ˢ s, f p.1 * f p.2).re := by
  rw [mul_pow, sq (∑ i ∈ s, f i), Finset.sum_mul_sum, ← Finset.sum_product',
    ← ofReal_pow, re_ofReal_mul]

end Complex
