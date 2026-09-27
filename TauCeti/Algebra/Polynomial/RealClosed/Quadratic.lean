/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
public import Mathlib.FieldTheory.IsRealClosed.Basic

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

/-! # Signs of irreducible quadratics over real closed fields

An irreducible quadratic over an ordered real closed field has negative discriminant.
Its value is therefore everywhere nonzero and has the sign of its leading coefficient.
The discriminant criterion also gives the converse characterization of irreducibility.
These facts supply the quadratic case of the algebraic polynomial intermediate value theorem.

The general sign calculation only requires an ordered field; real closedness is used to
turn a nonnegative discriminant into a square. The quadratic discriminant and root
criteria are those of `Mathlib.Algebra.QuadraticDiscriminant`.
-/

public section

namespace TauCeti
namespace Polynomial

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A quadratic with negative discriminant has the sign of its leading coefficient
at every argument. This implication holds over any ordered field. -/
theorem quadratic_pos_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hid : 4 * a * (a * x ^ 2 + b * x + c) =
      (2 * a * x + b) ^ 2 - discrim a b c := by
    rw [discrim]
    ring
  have hprod : 0 < a * (a * x ^ 2 + b * x + c) := by
    nlinarith [sq_nonneg (2 * a * x + b)]
  constructor
  · intro hx
    rcases lt_or_gt_of_ne (show a ≠ 0 by
      intro ha
      subst a
      simp only [discrim, zero_mul, mul_zero, sub_zero] at hd
      nlinarith [sq_nonneg b]) with ha | ha
    · nlinarith
    · exact ha
  · intro ha
    nlinarith

/-- With negative discriminant, a quadratic is negative everywhere exactly when
its leading coefficient is negative. -/
theorem quadratic_neg_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  have h := quadratic_pos_iff_of_discrim_neg (a := -a) (b := -b) (c := -c)
    (by simpa only [discrim_neg] using hd) x
  have heq : (C (-a) * X ^ 2 + C (-b) * X + C (-c)).eval x =
      -(C a * X ^ 2 + C b * X + C c).eval x := by
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  simpa only [heq, neg_pos] using h

variable [IsRealClosed R]

/-- A genuine quadratic over a real closed field is irreducible exactly when its
discriminant is negative. -/
theorem irreducible_quadratic_iff_discrim_neg {a b c : R} (ha : a ≠ 0) :
    Irreducible (C a * X ^ 2 + C b * X + C c) ↔ discrim a b c < 0 := by
  let p : R[X] := C a * X ^ 2 + C b * X + C c
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  constructor
  · intro hi
    by_contra hn
    have hd : 0 ≤ discrim a b c := le_of_not_gt hn
    obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare.mp hd)
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, hs⟩
    have hroot : p.IsRoot x := by
      simp only [p, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      nlinarith [hx]
    exact (hi.not_isRoot_of_natDegree_ne_one (by rw [hdeg]; decide)) hroot
  · intro hd
    have hnot : ∀ x, ¬ p.IsRoot x := by
      intro x hroot
      have hx : a * x ^ 2 + b * x + c = 0 := by
        simpa only [p, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] using hroot
      have hs := discrim_eq_sq_of_quadratic_eq_zero
        (a := a) (b := b) (c := c) (x := x) (by simpa only [sq] using hx)
      nlinarith [sq_nonneg (2 * a * x + b)]
    exact irreducible_of_degree_le_three_of_not_isRoot (p := p)
      (by rw [Finset.mem_Icc, hdeg]; decide) hnot

/-- The value of an irreducible quadratic over a real closed field has the sign
of its leading coefficient. -/
theorem irreducible_quadratic_eval_pos_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  exact quadratic_pos_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- The negative-sign counterpart of `irreducible_quadratic_eval_pos_iff`. -/
theorem irreducible_quadratic_eval_neg_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  exact quadratic_neg_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- An irreducible polynomial of degree two has everywhere the sign of its
leading coefficient. This form can be used without choosing a coefficient presentation. -/
theorem irreducible_eval_pos_iff_leadingCoeff_pos {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : 0 < p.eval x ↔ 0 < p.leadingCoeff := by
  have hrepr : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    rw [p.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
    simp [Finset.sum_range_succ]
    ring
  have ha : p.coeff 2 ≠ 0 := by
    simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
  have h := irreducible_quadratic_eval_pos_iff ha (hrepr ▸ hi) x
  rw [← hrepr] at h
  simpa only [leadingCoeff, hdeg] using h

/-- The negative-sign form for an arbitrary irreducible quadratic. -/
theorem irreducible_eval_neg_iff_leadingCoeff_neg {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : p.eval x < 0 ↔ p.leadingCoeff < 0 := by
  have hrepr : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    rw [p.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
    simp [Finset.sum_range_succ]
    ring
  have ha : p.coeff 2 ≠ 0 := by
    simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
  have h := irreducible_quadratic_eval_neg_iff ha (hrepr ▸ hi) x
  rw [← hrepr] at h
  simpa only [leadingCoeff, hdeg] using h

end Polynomial
end TauCeti
