/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Algebra.Squarefree

/-!
# The squarefree part of a rational number

Every nonzero rational number `u` can be written uniquely as `u = d * c ^ 2` with `d` a squarefree
integer and `c` a nonzero rational (`Rat.exists_squarefree_int_mul_sq` and
`Rat.eq_of_squarefree_of_intCast_mul_sq_eq`). This file names that integer `Rat.squarefreePart u`,
with the convention `Rat.squarefreePart 0 = 0`. It is the canonical integer representative of the
square class of `u` in `ℚˣ / (ℚˣ) ^ 2`: it keeps the sign of `u`, it is unchanged by multiplying
`u` by a nonzero square, and a prime divides it exactly when the `p`-adic valuation of `u` is odd.
Square-class invariants of rationals, such as the quadratic field `ℚ(√u)` or the quadratic
Dirichlet character attached to `u`, can therefore be defined through this integer.

## Main definitions and results

* `Rat.squarefreePart`: the squarefree part `ℚ → ℤ`.
* `Rat.squarefree_squarefreePart`, `Rat.exists_eq_squarefreePart_mul_sq`: for `u ≠ 0` it is
  squarefree and `u` is it times a nonzero rational square.
* `Rat.squarefreePart_eq_iff`: for squarefree `d`, `Rat.squarefreePart u = d` exactly when
  `u = d * c ^ 2` for a nonzero rational `c`.
* `Rat.squarefreePart_mul_sq`: invariance under multiplication by a nonzero square.
* `Rat.squarefreePart_pos_iff`, `Rat.squarefreePart_neg_iff`: it has the sign of `u`.
* `Rat.prime_dvd_squarefreePart_iff`: a prime `p` divides it exactly when `padicValRat p u` is odd.

## References

* V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., Exercise 1.30.
-/

public section

namespace Rat

/-- **The squarefree part of a rational number.** For `u ≠ 0` this is the unique squarefree
integer `d` such that `u = d * c ^ 2` for some nonzero rational `c` (`Rat.squarefreePart_eq_iff`);
its sign is the sign of `u`. By convention the squarefree part of `0` is `0`. -/
noncomputable def squarefreePart (u : ℚ) : ℤ :=
  if hu : u = 0 then 0 else (exists_squarefree_int_mul_sq hu).choose

/-- The squarefree part of a nonzero rational is squarefree and represents its square class. -/
private theorem squarefreePart_spec {u : ℚ} (hu : u ≠ 0) :
    Squarefree u.squarefreePart ∧ ∃ c : ℚ, c ≠ 0 ∧ u = u.squarefreePart * c ^ 2 := by
  simp only [squarefreePart, hu, ↓reduceDIte]
  obtain ⟨c, hsf, hc, h⟩ := (exists_squarefree_int_mul_sq hu).choose_spec
  exact ⟨hsf, c, hc, h⟩

/-- The squarefree part of `0` is `0`, by convention. -/
@[simp]
theorem squarefreePart_zero : squarefreePart 0 = 0 := by
  simp [squarefreePart]

/-- The squarefree part of a nonzero rational number is squarefree. -/
theorem squarefree_squarefreePart {u : ℚ} (hu : u ≠ 0) : Squarefree u.squarefreePart :=
  (squarefreePart_spec hu).1

/-- A nonzero rational number is its squarefree part times the square of a nonzero rational. -/
theorem exists_eq_squarefreePart_mul_sq {u : ℚ} (hu : u ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ u = u.squarefreePart * c ^ 2 :=
  (squarefreePart_spec hu).2

/-- **Characterisation of the squarefree part.** For a squarefree integer `d`, the squarefree part
of `u` is `d` exactly when `u` is `d` times the square of a nonzero rational. -/
theorem squarefreePart_eq_iff {u : ℚ} {d : ℤ} (hd : Squarefree d) :
    u.squarefreePart = d ↔ ∃ c : ℚ, c ≠ 0 ∧ u = d * c ^ 2 := by
  constructor
  · rintro rfl
    have hu : u ≠ 0 := by
      rintro rfl
      simp at hd
    exact exists_eq_squarefreePart_mul_sq hu
  · rintro ⟨c, hc, rfl⟩
    have hu : (d : ℚ) * c ^ 2 ≠ 0 := mul_ne_zero (by exact_mod_cast hd.ne_zero) (by positivity)
    obtain ⟨c', hc', h⟩ := exists_eq_squarefreePart_mul_sq hu
    exact eq_of_squarefree_of_intCast_mul_sq_eq (squarefree_squarefreePart hu) hd hc' h.symm

/-- The squarefree part vanishes only at `0`. -/
@[simp]
theorem squarefreePart_eq_zero_iff {u : ℚ} : u.squarefreePart = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ squarefreePart_zero⟩
  by_contra hu
  exact (squarefree_squarefreePart hu).ne_zero h

/-- The squarefree part of a nonzero rational number is nonzero. -/
theorem squarefreePart_ne_zero {u : ℚ} (hu : u ≠ 0) : u.squarefreePart ≠ 0 :=
  squarefreePart_eq_zero_iff.not.mpr hu

/-- The squarefree part of a squarefree integer is the integer itself. -/
theorem squarefreePart_intCast_of_squarefree {d : ℤ} (hd : Squarefree d) :
    (d : ℚ).squarefreePart = d :=
  (squarefreePart_eq_iff hd).mpr ⟨1, one_ne_zero, by simp⟩

/-- The square class of `1` is represented by `1`. -/
@[simp]
theorem squarefreePart_one : squarefreePart 1 = 1 := by
  simpa using squarefreePart_intCast_of_squarefree squarefree_one

/-- **The squarefree part is constant on square classes.** Multiplying by the square of a nonzero
rational does not change the squarefree part. -/
@[simp]
theorem squarefreePart_mul_sq (u : ℚ) {t : ℚ} (ht : t ≠ 0) :
    (u * t ^ 2).squarefreePart = u.squarefreePart := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨c, hc, h⟩ := exists_eq_squarefreePart_mul_sq hu
  refine (squarefreePart_eq_iff (squarefree_squarefreePart hu)).mpr ⟨c * t, mul_ne_zero hc ht, ?_⟩
  rw [mul_pow, ← mul_assoc, ← h]

/-- A rational number and its inverse have the same squarefree part. -/
@[simp]
theorem squarefreePart_inv (u : ℚ) : u⁻¹.squarefreePart = u.squarefreePart := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [← squarefreePart_mul_sq u⁻¹ hu, sq, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

/-- Negating a rational number negates its squarefree part. -/
@[simp]
theorem squarefreePart_neg (u : ℚ) : (-u).squarefreePart = -u.squarefreePart := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨c, hc, h⟩ := exists_eq_squarefreePart_mul_sq hu
  refine (squarefreePart_eq_iff (squarefree_squarefreePart hu).neg).mpr ⟨c, hc, ?_⟩
  rw [Int.cast_neg, neg_mul, ← h]

/-- The squarefree part of `u` is positive exactly when `u` is. -/
@[simp]
theorem squarefreePart_pos_iff {u : ℚ} : 0 < u.squarefreePart ↔ 0 < u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨c, hc, h⟩ := exists_eq_squarefreePart_mul_sq hu
  conv_rhs => rw [h]
  rw [mul_pos_iff_of_pos_right (by positivity), Int.cast_pos]

/-- The squarefree part of `u` is negative exactly when `u` is. -/
@[simp]
theorem squarefreePart_neg_iff {u : ℚ} : u.squarefreePart < 0 ↔ u < 0 := by
  simpa using squarefreePart_pos_iff (u := -u)

/-- **The primes dividing the squarefree part.** For a nonzero rational `u` and a prime `p`, the
prime `p` divides the squarefree part of `u` exactly when the `p`-adic valuation of `u` is odd. -/
theorem prime_dvd_squarefreePart_iff {u : ℚ} (hu : u ≠ 0) {p : ℕ} [hp : Fact p.Prime] :
    (p : ℤ) ∣ u.squarefreePart ↔ Odd (padicValRat p u) := by
  obtain ⟨c, hc, h⟩ := exists_eq_squarefreePart_mul_sq hu
  have hsf := squarefree_squarefreePart hu
  set d := u.squarefreePart
  have hd : d ≠ 0 := hsf.ne_zero
  -- The valuation of `d * c ^ 2` is that of `d` plus an even number.
  have hval : padicValRat p u = padicValInt p d + 2 * padicValRat p c := by
    rw [h, padicValRat.mul (by exact_mod_cast hd) (by positivity), padicValRat.pow,
      padicValRat.of_int]
    push_cast
    ring
  -- Since `d` is squarefree, its valuation is at most one.
  have hle : padicValInt p d ≤ 1 := by
    by_contra! hlt
    have hp2 : (p : ℤ) ^ 2 ∣ d := (padicValInt_dvd_iff 2 d).mpr (Or.inr hlt)
    exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit (hsf _ (by simpa [sq] using hp2))
  have hdvd : (p : ℤ) ∣ d ↔ 1 ≤ padicValInt p d := by
    simpa [hd] using padicValInt_dvd_iff (p := p) 1 d
  rw [hdvd, hval, Int.odd_add, Int.odd_coe_nat]
  simp only [even_two, Even.mul_right, iff_true]
  rw [Nat.odd_iff]
  omega

end Rat

/-! ### Examples -/

/-- The worked example `8 / 9 = 2 * (2 / 3) ^ 2`. -/
example : (8 / 9 : ℚ).squarefreePart = 2 :=
  (Rat.squarefreePart_eq_iff Int.prime_two.squarefree).mpr ⟨2 / 3, by norm_num, by norm_num⟩

/-- The sign is kept: `-12 = -3 * 2 ^ 2`. -/
example : (-12 : ℚ).squarefreePart = -3 :=
  (Rat.squarefreePart_eq_iff Int.prime_three.squarefree.neg).mpr ⟨2, by norm_num, by norm_num⟩

/-- `-1` is not in the square class of `1`, so a definition through `|u|` would be wrong. -/
example : (-1 : ℚ).squarefreePart = -1 := by
  simp

/-- `3 / 4 = 3 * (1 / 2) ^ 2`. -/
example : (3 / 4 : ℚ).squarefreePart = 3 :=
  (Rat.squarefreePart_eq_iff Int.prime_three.squarefree).mpr ⟨1 / 2, by norm_num, by norm_num⟩
