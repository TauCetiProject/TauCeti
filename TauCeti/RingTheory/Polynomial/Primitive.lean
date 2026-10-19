/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Primitive polynomial comparisons

A primitive polynomial divisible by a polynomial of at least its degree differs
from it by a constant unit. Reversal permutes the coefficients and hence preserves
primitivity. Together these facts compare primitive defining polynomials after
inversion of a root.
-/

public section

open Polynomial

namespace TauCeti

/-- Reversal preserves primitivity, including for polynomials with zero constant term. -/
@[simp]
theorem _root_.Polynomial.isPrimitive_reverse_iff {R : Type*} [CommSemiring R] (p : R[X]) :
    p.reverse.IsPrimitive ↔ p.IsPrimitive := by
  simp only [Polynomial.IsPrimitive]
  constructor <;> intro h r hr <;> apply h r <;>
    rw [C_dvd_iff_dvd_coeff] at hr ⊢ <;> intro i
  · simpa only [coeff_reverse] using hr (revAt p.natDegree i)
  · simpa only [coeff_reverse, revAt_invol] using hr (revAt p.natDegree i)

/-- A primitive polynomial divisible by a polynomial of at least its degree
is the latter times a constant unit. -/
theorem _root_.Polynomial.IsPrimitive.exists_eq_mul_C_unit_of_dvd_of_natDegree_le
    {R : Type*} [CommSemiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p.IsPrimitive)
    (hdvd : q ∣ p) (hdeg : p.natDegree ≤ q.natDegree) :
    ∃ u : Rˣ, p = q * C (u : R) := by
  nontriviality R
  obtain ⟨r, rfl⟩ := hdvd
  have hq : q ≠ 0 := left_ne_zero_of_mul hp.ne_zero
  have hr : r ≠ 0 := right_ne_zero_of_mul hp.ne_zero
  have hrdeg : r.natDegree = 0 := by
    rw [natDegree_mul hq hr] at hdeg
    omega
  rw [eq_C_of_natDegree_eq_zero hrdeg] at hp ⊢
  obtain ⟨u, hu⟩ := (isPrimitive_iff_isUnit_of_C_dvd.mp hp) _ (dvd_mul_left _ _)
  exact ⟨u, by rw [hu]⟩

end TauCeti
