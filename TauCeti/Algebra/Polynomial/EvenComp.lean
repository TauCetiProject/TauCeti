/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand

/-!
# Even polynomials are polynomials in `X²`

A polynomial fixed by the substitution `X ↦ -X`, over a coefficient ring without additive torsion,
is a polynomial in `X²`. This is the invariant theory of the group of order two acting on a line.
Translating by `1` gives the same statement for the reflection `X ↦ -X - 2`, whose invariant is
`X² + 2X`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- **An even polynomial is a polynomial in `X²`.** -/
theorem exists_eq_comp_X_sq_of_comp_neg_X_eq {p : R[X]} (hp : p.comp (-X) = p) :
    ∃ r : R[X], p = r.comp (X ^ 2) := by
  refine ⟨contract 2 p, ?_⟩
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand two_pos]
  split_ifs with hn
  · rw [coeff_contract two_ne_zero, Nat.div_mul_cancel hn]
  · have hc := congrArg (fun q : R[X] ↦ q.coeff n) hp
    have hneg : (-X : R[X]) = C (-1) * X := by simp
    simp only [hneg, comp_C_mul_X_coeff] at hc
    rw [(Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])).neg_one_pow, mul_neg_one] at hc
    exact neg_eq_self.mp hc

/-- **A polynomial invariant under `X ↦ -X - 2` is a polynomial in `X² + 2X`.** -/
theorem exists_eq_comp_X_sq_add_two_mul_X_of_comp_neg_X_sub_two_eq {q : R[X]}
    (hq : q.comp (-X - 2) = q) : ∃ r : R[X], q = r.comp (X ^ 2 + 2 * X) := by
  have hq₁ : (q.comp (X - 1)).comp (-X) = q.comp (X - 1) := by
    conv_rhs => rw [← hq]
    rw [comp_assoc, comp_assoc]
    congr 1
    simp only [sub_comp, X_comp, one_comp, neg_comp, ofNat_comp]
    ring
  obtain ⟨r, hr⟩ := exists_eq_comp_X_sq_of_comp_neg_X_eq hq₁
  refine ⟨r.comp (X + 1), ?_⟩
  have hcomp := congrArg (·.comp (X + 1)) hr
  simp only [comp_assoc, sub_comp, X_comp, one_comp, pow_comp] at hcomp
  rw [show ((X : R[X]) + 1 - 1) = X by ring, comp_X] at hcomp
  rw [hcomp, comp_assoc]
  congr 1
  simp only [add_comp, X_comp, one_comp]
  ring

end Polynomial
