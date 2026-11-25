/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Vanishing and denominators of the `p`-adic valuation of a rational number

This file characterises when the `p`-adic valuation of a nonzero rational number vanishes,
compares the valuations of two rational numbers with sum `1`, and reads the multiplicity of `p` in
the denominator of a rational number off its valuation.

## Main results

* `padicValRat.eq_zero_iff`: a nonzero rational number has `p`-adic valuation zero
  exactly when `p` divides neither its numerator nor its denominator.
* `padicValRat.eq_zero_of_add_eq_one_of_pos` and `padicValRat.eq_of_add_eq_one_of_neg`: if
  `x + y = 1`, then `v_p(x) > 0` forces `v_p(y) = 0`, and `v_p(x) < 0` forces `v_p(y) = v_p(x)`.
* `padicValRat.max_natAbs_eq_of_add_eq_one`: if `x + y = 1`, then `x` and `y` have the common
  denominator `w = x.den`, and `max(|v_p(x)|, |v_p(y)|)` is the largest of the valuations of the
  three terms of `x.num + y.num = w`.
* `padicValRat.toNat_neg`: the multiplicity of `p` in the denominator of `q` is the negative part
  of `v_p(q)`.
* `Rat.multiplicity_den_add_of_lt`: if `p` divides the denominator of `r` to a higher power than
  that of `q`, then it divides the denominator of `q + r` to the same power as that of `r`.
-/

public section

namespace padicValRat

/-- A nonzero rational number has `p`-adic valuation zero exactly when the prime `p` divides
neither its numerator nor its denominator. -/
theorem eq_zero_iff {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q = 0 ↔ ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
  have hnum : padicValInt p q.num = 0 ↔ ¬ p ∣ q.num.natAbs := by
    simp [padicValInt, Nat.multiplicity_eq_zero_iff, hp.out.ne_one, hq]
  have hden : padicValNat p q.den = 0 ↔ ¬ p ∣ q.den := by
    simp [Nat.padicValNat_def, Nat.multiplicity_eq_zero_iff, hp.out.ne_one]
  simp only [Nat.padicValNat_def] at hden ⊢
  rw [padicValRat_def, ← hnum, ← hden]
  rcases Rat.num_or_den_zero_padicVal q hp.out with h | h <;> simp [h, hp.out.ne_one, hq]

/-- If `x + y = 1` and `x` has positive `p`-adic valuation, then `y` has `p`-adic valuation
zero. -/
theorem eq_zero_of_add_eq_one_of_pos {p : ℕ} [Fact p.Prime] {x y : ℚ} (hxy : x + y = 1)
    (hx : 0 < padicValRat p x) : padicValRat p y = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy' : 1 + -x = y := by linarith
  have h := add_eq_of_lt (p := p) (q := 1) (r := -x) (hy'.symm ▸ hy) one_ne_zero
    (neg_ne_zero.2 hx0) (by rwa [padicValRat.one, padicValRat.neg])
  rwa [padicValRat.one, hy'] at h

/-- If `x + y = 1` and `x` has negative `p`-adic valuation, then `y` has the same `p`-adic
valuation as `x`. -/
theorem eq_of_add_eq_one_of_neg {p : ℕ} [Fact p.Prime] {x y : ℚ} (hxy : x + y = 1)
    (hx : padicValRat p x < 0) : padicValRat p y = padicValRat p x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy' : -x + 1 = y := by linarith
  have hy : y ≠ 0 := by rintro rfl; rw [add_zero] at hxy; simp [hxy] at hx
  have h := add_eq_of_lt (p := p) (q := -x) (r := 1) (hy'.symm ▸ hy) (neg_ne_zero.2 hx0)
    one_ne_zero (by rwa [padicValRat.one, padicValRat.neg])
  rwa [padicValRat.neg, hy'] at h

/-- If `x + y = 1`, write `x = u / w` and `y = v / w` in lowest terms, with `u = x.num`,
`v = y.num` and the common denominator `w = x.den`, so that `u + v = w`. Then at every prime `p`
the larger of `|v_p(x)|` and `|v_p(y)|` is the largest of `v_p(u)`, `v_p(v)` and `v_p(w)`. -/
theorem max_natAbs_eq_of_add_eq_one {p : ℕ} [hp : Fact p.Prime] {x y : ℚ} (hxy : x + y = 1) :
    max (padicValRat p x).natAbs (padicValRat p y).natAbs =
      max (padicValInt p x.num) (max (padicValInt p y.num) (padicValNat p x.den)) := by
  have hden : y.den = x.den := by rw [eq_sub_of_add_eq' hxy]; simp
  have h₁ := eq_zero_of_add_eq_one_of_pos (p := p) hxy
  have h₂ := eq_zero_of_add_eq_one_of_pos (p := p) ((add_comm y x).trans hxy)
  -- a prime cannot divide both the numerator and the denominator of `x`, or of `y`
  have hx := Rat.num_or_den_zero_padicVal x hp.out
  have hy := Rat.num_or_den_zero_padicVal y hp.out
  simp only [padicValRat_def, hden, Nat.padicValNat_def] at h₁ h₂ hx hy ⊢
  omega

/-- The `p`-adic valuation of a rational number is at least minus the multiplicity of `p` in its
denominator. -/
theorem neg_multiplicity_den_le (p : ℕ) (q : ℚ) :
    -(multiplicity p q.den : ℤ) ≤ padicValRat p q := by
  rw [padicValRat_def]
  omega

/-- At a prime `p`, the multiplicity of `p` in the denominator of a rational number is the
negative part of its `p`-adic valuation. -/
theorem toNat_neg {p : ℕ} [hp : Fact p.Prime] (q : ℚ) :
    (-padicValRat p q).toNat = multiplicity p q.den := by
  rw [padicValRat_def]
  rcases Rat.num_or_den_zero_padicVal q hp.out with h | h <;> omega

end padicValRat

namespace Rat

/-- **Ultrametric property of the denominator.** If `p` divides the denominator of `r` to a higher
power than that of `q`, then it divides the denominator of `q + r` to exactly the same power as
that of `r`. -/
theorem multiplicity_den_add_of_lt {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (h : multiplicity p q.den < multiplicity p r.den) :
    multiplicity p (q + r).den = multiplicity p r.den := by
  have hr := padicValRat.toNat_neg (p := p) r
  have hq := padicValRat.neg_multiplicity_den_le p q
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at h
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hlt : padicValRat p r < padicValRat p q := by omega
  have hrq : r + q ≠ 0 := fun h0 ↦ by
    rw [eq_neg_of_add_eq_zero_left h0, padicValRat.neg] at hlt
    exact hlt.false
  rw [← padicValRat.toNat_neg, add_comm, padicValRat.add_eq_of_lt hrq hr0 hq0 hlt, hr]

end Rat
