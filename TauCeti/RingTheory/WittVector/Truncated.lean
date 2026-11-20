/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Truncated
public import TauCeti.RingTheory.WittVector.Units

/-!
# The first two coordinates of truncated Witt vectors

Let `p` be a prime and `R` any commutative ring (with no torsion hypothesis). The first
coordinates of a sum of Witt vectors are `(x + y)₀ = x₀ + y₀` and
`(x + y)₁ = x₁ + y₁ + C_p(x₀, y₀)` (`WittVector.add_coeff_one`), where
`C_p = TauCeti.DeltaRing.addCorrection p` is the integral polynomial
`(X ^ p + Y ^ p - (X + Y) ^ p) / p`; together with the product formula
`(x * y)₁ = x₀ ^ p * y₁ + y₀ ^ p * x₁ + p * x₁ * y₁` (`WittVector.mul_coeff_one`) these are the
sum and product rules of a `δ`-structure.

We transfer these formulas to the truncated Witt vectors `TruncatedWittVector p n R` of length
at least two, and show that a length-two Witt vector `(z₀, z₁)` is a unit exactly when `z₀` and
its first ghost component `z₀ ^ p + p * z₁` are units.

## Main results

* `TruncatedWittVector.add_coeff_one`, `TruncatedWittVector.mul_coeff_one`: the first coordinate
  of a sum and a product of truncated Witt vectors of length at least two.
* `TruncatedWittVector.isUnit_iff_isUnit_coeff_zero_and_ghost_one`: the units of the length-two
  Witt vectors.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Remark 2.4 and the proof of Lemma 2.15.
-/

public section

namespace TruncatedWittVector

variable {p n : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- The zeroth coordinate of `1` is `1`. -/
@[simp]
theorem one_coeff_zero : (1 : TruncatedWittVector p (n + 1) R).coeff 0 = 1 := by
  rw [← map_one (WittVector.truncate (p := p) (R := R) (n + 1)), WittVector.coeff_truncate]
  exact WittVector.one_coeff_zero p R

/-- The first coordinate of `1` is `0`. -/
@[simp]
theorem one_coeff_one : (1 : TruncatedWittVector p (n + 2) R).coeff 1 = 0 := by
  rw [← map_one (WittVector.truncate (p := p) (R := R) (n + 2)), WittVector.coeff_truncate]
  exact WittVector.one_coeff_eq_of_pos p R _ (by simp)

/-- The zeroth coordinate of a sum of truncated Witt vectors is the sum of their zeroth
coordinates. -/
@[simp]
theorem add_coeff_zero (x y : TruncatedWittVector p (n + 1) R) :
    (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  simp only [← map_add, WittVector.coeff_truncate, Fin.val_zero, WittVector.add_coeff_zero]

/-- The zeroth coordinate of a product of truncated Witt vectors is the product of their zeroth
coordinates. -/
@[simp]
theorem mul_coeff_zero (x y : TruncatedWittVector p (n + 1) R) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  simp only [← map_mul, WittVector.coeff_truncate, Fin.val_zero, WittVector.mul_coeff_zero]

/-- The first coordinate of a sum of truncated Witt vectors of length at least two is
`x₁ + y₁ + C_p(x₀, y₀)`. -/
theorem add_coeff_one (x y : TruncatedWittVector p (n + 2) R) :
    (x + y).coeff 1 =
      x.coeff 1 + y.coeff 1 + TauCeti.DeltaRing.addCorrection p (x.coeff 0) (y.coeff 0) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 2) R x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 2) R y
  simp only [← map_add, WittVector.coeff_truncate, Fin.val_zero, Fin.val_one,
    WittVector.add_coeff_one]

/-- The first coordinate of a product of truncated Witt vectors of length at least two is
`x₀ ^ p * y₁ + y₀ ^ p * x₁ + p * x₁ * y₁`. -/
theorem mul_coeff_one (x y : TruncatedWittVector p (n + 2) R) :
    (x * y).coeff 1 =
      x.coeff 0 ^ p * y.coeff 1 + y.coeff 0 ^ p * x.coeff 1 + p * x.coeff 1 * y.coeff 1 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 2) R x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 2) R y
  simp only [← map_mul, WittVector.coeff_truncate, Fin.val_zero, Fin.val_one,
    WittVector.mul_coeff_one]

/-- A length-two Witt vector `z = (z₀, z₁)` is a unit if and only if both `z₀` and its first
ghost component `z₀ ^ p + p * z₁` are units. -/
theorem isUnit_iff_isUnit_coeff_zero_and_ghost_one (z : TruncatedWittVector p 2 R) :
    IsUnit z ↔ IsUnit (z.coeff 0) ∧ IsUnit (z.coeff 0 ^ p + p * z.coeff 1) := by
  constructor
  · rintro ⟨u, rfl⟩
    set w : TruncatedWittVector p 2 R := ↑u⁻¹
    have h₀ := congrArg (coeff 0) u.mul_inv
    have h₁ := congrArg (coeff 1) u.mul_inv
    rw [mul_coeff_zero, one_coeff_zero] at h₀
    rw [mul_coeff_one, one_coeff_one] at h₁
    have h₀p : ((u : TruncatedWittVector p 2 R).coeff 0 * w.coeff 0) ^ p = 1 := by
      rw [h₀, one_pow]
    -- The first ghost component is multiplicative, so `w₀ ^ p + p * w₁` inverts
    -- `z₀ ^ p + p * z₁`.
    refine ⟨.of_mul_eq_one _ h₀, .of_mul_eq_one (w.coeff 0 ^ p + p * w.coeff 1) ?_⟩
    linear_combination h₀p + (p : R) * h₁
  · rintro ⟨ha, hg⟩
    obtain ⟨a', ha'⟩ := ha.exists_right_inv
    obtain ⟨g', hg'⟩ := hg.exists_right_inv
    -- The inverse is `(a', -a' ^ p * z₁ * g')`, where `a'` inverts `z₀` and `g'` inverts
    -- `z₀ ^ p + p * z₁`.
    refine .of_mul_eq_one (mk p ![a', -(a' ^ p * z.coeff 1 * g')]) (ext fun i => ?_)
    fin_cases i
    · simp [coeff_mk, ha']
    · simp only [Fin.mk_one, mul_coeff_one, one_coeff_one, coeff_mk]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
      linear_combination (-(a' ^ p * z.coeff 1)) * hg'

end TruncatedWittVector
