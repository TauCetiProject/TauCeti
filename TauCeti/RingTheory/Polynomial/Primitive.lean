/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.Content

/-!
# A divisor of the highest possible degree, and primitive polynomial comparisons

A polynomial divisible by a polynomial of at least its degree is the latter times a constant, and
the constant is a unit when the multiple is primitive
(`Polynomial.IsPrimitive.exists_eq_mul_C_unit_of_dvd_of_natDegree_le`). Reversal permutes the
coefficients and hence preserves primitivity. Together these facts compare primitive defining
polynomials after inversion of a root.
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

/-- **A divisor of the highest possible degree is a constant multiple.** If `q ∣ p` and `p` has
degree at most that of `q`, then `p = q * C c` for the constant term `c` of the quotient, and the
leading coefficient of `p` is that of `q` times `c`. With `p` primitive in addition, `c` is a unit
(`Polynomial.IsPrimitive.exists_eq_mul_C_unit_of_dvd_of_natDegree_le`). -/
theorem _root_.Polynomial.exists_eq_mul_C_of_dvd_of_natDegree_le {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] {p q : R[X]} (hdvd : q ∣ p) (hdeg : p.natDegree ≤ q.natDegree) :
    ∃ c : R, p = q * C c ∧ p.leadingCoeff = q.leadingCoeff * c := by
  obtain ⟨r, rfl⟩ := hdvd
  by_cases hq : q = 0
  · exact ⟨r.coeff 0, by simp [hq], by simp [hq]⟩
  by_cases hr : r = 0
  · exact ⟨0, by simp [hr], by simp [hr]⟩
  have hrdeg : r.natDegree = 0 := by
    rw [natDegree_mul hq hr] at hdeg
    omega
  refine ⟨r.coeff 0, by rw [← eq_C_of_natDegree_eq_zero hrdeg], ?_⟩
  conv_lhs => rw [eq_C_of_natDegree_eq_zero hrdeg]
  rw [leadingCoeff_mul, leadingCoeff_C]

/-- A primitive polynomial divisible by a polynomial of at least its degree
is the latter times a constant unit. -/
theorem _root_.Polynomial.IsPrimitive.exists_eq_mul_C_unit_of_dvd_of_natDegree_le
    {R : Type*} [CommSemiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p.IsPrimitive)
    (hdvd : q ∣ p) (hdeg : p.natDegree ≤ q.natDegree) :
    ∃ u : Rˣ, p = q * C (u : R) := by
  nontriviality R
  obtain ⟨c, hc, -⟩ := exists_eq_mul_C_of_dvd_of_natDegree_le hdvd hdeg
  obtain ⟨u, hu⟩ := isPrimitive_iff_isUnit_of_C_dvd.mp (hc ▸ hp) c (dvd_mul_left (C c) q)
  exact ⟨u, by rw [hc, hu]⟩

end TauCeti
