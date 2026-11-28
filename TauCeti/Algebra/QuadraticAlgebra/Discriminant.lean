/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Discriminants, nonnegative norms, and units in quadratic algebras

A ring map commutes with the discriminant (`QuadraticAlgebra.map_discr`). Over an ordered ring,
a nonpositive discriminant makes the norm nonnegative
(`QuadraticAlgebra.norm_nonneg_of_discr_nonpos`), as for `ℚ(√d)` with `d < 0`. Over `ℤ`, a
nonpositive discriminant forces every unit to have norm `1`
(`QuadraticAlgebra.norm_eq_one_of_discr_nonpos`), a negative discriminant forces every unit to be
`±1` or have `im = ±1` (`QuadraticAlgebra.units_re_or_im_of_discr_lt_zero`), and `discr a b < -4`
leaves only `±1` (`QuadraticAlgebra.units_eq_one_or_neg_one_of_discr_lt_neg_four`), so there are
exactly two units (`QuadraticAlgebra.natCard_units_eq_two_of_discr_lt_neg_four`).
-/

public section

namespace QuadraticAlgebra

/-- A ring map commutes with the discriminant. -/
theorem map_discr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (discr a b) = discr (f a) (f b) := by
  simp [discr_def, map_ofNat]

/-- **The norm is nonnegative when the discriminant is nonpositive.** Over an ordered ring, if
`b² + 4a ≤ 0` then every element of `QuadraticAlgebra R a b` has nonnegative norm. -/
theorem norm_nonneg_of_discr_nonpos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b : R} (h : discr a b ≤ 0) (z : QuadraticAlgebra R a b) :
    0 ≤ norm z := by
  have := im_sq_mul_discr z
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z.im) h, sq_nonneg (trace z)]

/-- **Units of a nonpositive-discriminant integral quadratic algebra have norm `1`.** -/
theorem norm_eq_one_of_discr_nonpos {a b : ℤ} (hd : discr a b ≤ 0)
    (u : (QuadraticAlgebra ℤ a b)ˣ) : norm (u : QuadraticAlgebra ℤ a b) = 1 := by
  have hunit : IsUnit (norm (u : QuadraticAlgebra ℤ a b)) := isUnit_iff_norm_isUnit.mp u.isUnit
  have hnonneg : 0 ≤ norm (u : QuadraticAlgebra ℤ a b) := norm_nonneg_of_discr_nonpos hd _
  rcases Int.isUnit_iff.mp hunit with h1 | h1 <;> omega

/-- **An integral unit with zero `im` coordinate is `1` or `-1`.** -/
theorem eq_one_or_neg_one_of_im_eq_zero {a b : ℤ} {u : (QuadraticAlgebra ℤ a b)ˣ}
    (him : (u : QuadraticAlgebra ℤ a b).im = 0) : u = 1 ∨ u = -1 := by
  have hunit : IsUnit ((u : QuadraticAlgebra ℤ a b).re ^ 2) := by
    simpa [norm_def, him, sq] using isUnit_iff_norm_isUnit.mp u.isUnit
  have hsq : (u : QuadraticAlgebra ℤ a b).re ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · nlinarith [sq_nonneg (u : QuadraticAlgebra ℤ a b).re]
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · exact .inl <| Units.ext <| by ext <;> simp [h1, him]
  · exact .inr <| Units.ext <| by ext <;> simp [h1, him]

/-- **Units of a negative-discriminant integral quadratic algebra**: when `discr a b < 0`, every
unit is either `±1` or has `im = ±1` (the latter occurring only at discriminants `-3` and `-4`). -/
theorem units_re_or_im_of_discr_lt_zero {a b : ℤ} (hd : discr a b < 0)
    (u : (QuadraticAlgebra ℤ a b)ˣ) :
    (u = 1 ∨ u = -1) ∨ ((u : QuadraticAlgebra ℤ a b).im = 1 ∨
      (u : QuadraticAlgebra ℤ a b).im = -1) := by
  by_cases him : (u : QuadraticAlgebra ℤ a b).im = 0
  · exact .inl (eq_one_or_neg_one_of_im_eq_zero him)
  · right
    have hd3 : discr a b ≤ -3 := by
      have := discr_emod_four_eq_zero_or_one a b
      omega
    have h4 := four_mul_norm_eq (u : QuadraticAlgebra ℤ a b)
    rw [norm_eq_one_of_discr_nonpos hd.le u, mul_one] at h4
    have him_pos : 0 < (u : QuadraticAlgebra ℤ a b).im ^ 2 := sq_pos_iff.mpr him
    have hbd : 3 * (u : QuadraticAlgebra ℤ a b).im ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (trace (u : QuadraticAlgebra ℤ a b)),
        sq_nonneg (u : QuadraticAlgebra ℤ a b).im]
    exact sq_eq_one_iff.mp (by omega)

/-- **Units for `discr a b < -4`**: in an integral quadratic algebra of discriminant strictly less
than `-4`, the only units are `1` and `-1`. -/
theorem units_eq_one_or_neg_one_of_discr_lt_neg_four {a b : ℤ} (hd : discr a b < -4)
    (u : (QuadraticAlgebra ℤ a b)ˣ) : u = 1 ∨ u = -1 := by
  rcases units_re_or_im_of_discr_lt_zero (by omega) u with h | him
  · exact h
  · exfalso
    have h4 := four_mul_norm_eq (u : QuadraticAlgebra ℤ a b)
    rw [norm_eq_one_of_discr_nonpos (by omega) u, mul_one] at h4
    have him_sq : (u : QuadraticAlgebra ℤ a b).im ^ 2 = 1 := by
      rcases him with h1 | h1 <;> simp [h1]
    rw [him_sq, mul_one] at h4
    nlinarith [sq_nonneg (trace (u : QuadraticAlgebra ℤ a b))]

/-- **Two units for `discr a b < -4`**: an integral quadratic algebra of discriminant strictly less
than `-4` has exactly the two units `1` and `-1`. -/
theorem natCard_units_eq_two_of_discr_lt_neg_four {a b : ℤ} (hd : discr a b < -4) :
    Nat.card (QuadraticAlgebra ℤ a b)ˣ = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨1, -1, fun h ↦ ?_, ?_⟩
  · have := congrArg (fun u : (QuadraticAlgebra ℤ a b)ˣ ↦ (u : QuadraticAlgebra ℤ a b).re) h
    simp at this
  · ext u
    simpa using units_eq_one_or_neg_one_of_discr_lt_neg_four hd u

end QuadraticAlgebra
