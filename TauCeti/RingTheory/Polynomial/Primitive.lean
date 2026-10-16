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
    {R : Type*} [CommSemiring R] [IsDomain R] {p q : R[X]} (hp : p.IsPrimitive)
    (hdvd : q ∣ p) (hdeg : p.natDegree ≤ q.natDegree) :
    ∃ u : Rˣ, p = q * C (u : R) := by
  have hq : q ≠ 0 := ne_zero_of_dvd_ne_zero hp.ne_zero hdvd
  obtain ⟨r, hr⟩ := hdvd
  have hr0 : r ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [hr, h, mul_zero]
  have hrdeg : r.natDegree = 0 := by
    rw [hr, natDegree_mul hq hr0] at hdeg
    omega
  have hrC : r = C (r.coeff 0) := eq_C_of_natDegree_eq_zero hrdeg
  have hu : IsUnit (r.coeff 0) :=
    (isPrimitive_iff_isUnit_of_C_dvd.mp hp) _
      ⟨q, hr.trans ((mul_comm q r).trans (congrArg (· * q) hrC))⟩
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, hr.trans (congrArg (q * ·) (hrC.trans (congrArg C hu.symm)))⟩

end TauCeti
