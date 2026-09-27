/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
public import Mathlib.FieldTheory.IsRealClosed.Basic

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Tactic

/-! # Signs of irreducible quadratics over real closed fields

An irreducible quadratic over an ordered real closed field has negative discriminant.
Its value is therefore everywhere nonzero and has the sign of its leading coefficient.
The discriminant criterion also gives the converse characterization of irreducibility.
These facts supply the quadratic case of the algebraic polynomial intermediate value theorem.

The general sign calculation in `TauCeti.Algebra.Polynomial.QuadraticDiscriminant` only
requires an ordered ring; real closedness is used to turn a nonnegative discriminant into a
square. The quadratic discriminant and root criteria are those of
`Mathlib.Algebra.QuadraticDiscriminant`.
-/

public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable [IsRealClosed R]

/-- A genuine quadratic over a real closed field is irreducible exactly when its
discriminant is negative. -/
@[simp]
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
      intro x
      have hsq : ∀ s : R, discrim a b c ≠ s ^ 2 := by
        intro s hs
        exact (not_le.mpr hd) (by rw [hs]; exact sq_nonneg s)
      simpa only [p, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, sq] using
        quadratic_ne_zero_of_discrim_ne_sq hsq x
    exact irreducible_of_degree_le_three_of_not_isRoot (p := p)
      (by rw [Finset.mem_Icc, hdeg]; decide) hnot

/-- Positivity of the value of an irreducible quadratic over a real closed field is equivalent
to positivity of its leading coefficient. -/
theorem irreducible_quadratic_eval_pos_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  exact quadratic_pos_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- The negative-sign counterpart of `irreducible_quadratic_eval_pos_iff`. -/
theorem irreducible_quadratic_eval_neg_iff {a b c : R} (ha : a ≠ 0)
    (hi : Irreducible (C a * X ^ 2 + C b * X + C c)) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  exact quadratic_neg_iff_of_discrim_neg ((irreducible_quadratic_iff_discrim_neg ha).mp hi) x

/-- The value of an irreducible polynomial of degree two is positive exactly when its leading
coefficient is positive. This form does not require a coefficient presentation. -/
@[simp]
theorem irreducible_quadratic_eval_pos_iff_leadingCoeff_pos {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : 0 < p.eval x ↔ 0 < p.leadingCoeff := by
  have hrepr := eq_quadratic_of_degree_le_two (p := p) (degree_le_of_natDegree_le hdeg.le)
  have ha : p.coeff 2 ≠ 0 := by
    simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
  have h := irreducible_quadratic_eval_pos_iff ha (hrepr ▸ hi) x
  rw [← hrepr] at h
  simpa only [leadingCoeff, hdeg] using h

/-- The negative-sign form for an arbitrary irreducible quadratic. -/
@[simp]
theorem irreducible_quadratic_eval_neg_iff_leadingCoeff_neg {p : R[X]} (hi : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : p.eval x < 0 ↔ p.leadingCoeff < 0 := by
  have hrepr := eq_quadratic_of_degree_le_two (p := p) (degree_le_of_natDegree_le hdeg.le)
  have ha : p.coeff 2 ≠ 0 := by
    simpa only [leadingCoeff, hdeg] using (leadingCoeff_ne_zero.mpr hi.ne_zero)
  have h := irreducible_quadratic_eval_neg_iff ha (hrepr ▸ hi) x
  rw [← hrepr] at h
  simpa only [leadingCoeff, hdeg] using h

end TauCeti
