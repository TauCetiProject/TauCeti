/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Normed.Ring.ElementarySymmetric

/-!
# The `T₂` root norm of a polynomial

The sum of the squared absolute values of the roots (with multiplicity) is the first quantity
minimized when choosing a canonical defining polynomial, as described in the LMFDB knowl
[`nf.polredabs`](https://www.lmfdb.org/knowledge/show/nf.polredabs). It is not the sum of the
squares of the complex roots. We extend it to the zero polynomial using its empty root multiset.

Vieta's formula and the root-mean-square bound on elementary symmetric functions give a
binomial coefficient bound on each coefficient of a monic polynomial in terms of its `T₂`.
-/

public section

namespace Polynomial

/-- The sum of the squared absolute values of the complex roots, counted with multiplicity. -/
noncomputable def complexT2 (p : ℂ[X]) : ℝ := (p.roots.map fun z ↦ ‖z‖ ^ 2).sum

/-- The root sum giving the `T₂` norm of a complex polynomial. -/
theorem complexT2_def (p : ℂ[X]) : p.complexT2 = (p.roots.map fun z ↦ ‖z‖ ^ 2).sum := (rfl)

/-- A constant complex polynomial has root norm zero. -/
@[simp] theorem complexT2_C (a : ℂ) : (C a).complexT2 = 0 := by simp [complexT2_def]

/-- The empty-root convention gives the zero polynomial root norm zero. -/
@[simp] theorem complexT2_zero : (0 : ℂ[X]).complexT2 = 0 := by simp [complexT2_def]

/-- The unit polynomial has root norm zero. -/
@[simp] theorem complexT2_one : (1 : ℂ[X]).complexT2 = 0 := by simp [complexT2_def]

/-- The root norm of a monic linear polynomial is the squared norm of its root. -/
@[simp] theorem complexT2_X_sub_C (z : ℂ) : (X - C z).complexT2 = ‖z‖ ^ 2 := by
  simp [complexT2_def]

/-- The complex root norm is nonnegative. -/
@[simp, grind ←] theorem complexT2_nonneg (p : ℂ[X]) : 0 ≤ p.complexT2 := by
  rw [complexT2_def]
  exact Multiset.sum_nonneg fun _ h ↦ by
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp h
    exact sq_nonneg ‖z‖

/-- The root norm is unchanged by nonzero scalar multiplication. -/
@[simp] theorem complexT2_C_mul (p : ℂ[X]) {a : ℂ} (ha : a ≠ 0) :
    (C a * p).complexT2 = p.complexT2 := by simp [complexT2_def, roots_C_mul p ha]

/-- The root norm is additive under multiplication of nonzero polynomials. -/
theorem complexT2_mul {p q : ℂ[X]} (h : p * q ≠ 0) :
    (p * q).complexT2 = p.complexT2 + q.complexT2 := by
  simp [complexT2_def, roots_mul h]

/-- The `T₂` norm of an integer polynomial, computed on its complex coefficient image. -/
noncomputable def t2 (p : ℤ[X]) : ℝ := (p.map (Int.castRingHom ℂ)).complexT2

/-- The integer root norm agrees with the root norm after mapping the coefficients to `ℂ`. -/
theorem t2_def (p : ℤ[X]) : p.t2 = (p.map (Int.castRingHom ℂ)).complexT2 := (rfl)

/-- A constant integer polynomial has root norm zero. -/
@[simp] theorem t2_intCast (a : ℤ) : (a : ℤ[X]).t2 = 0 := by
  rw [← eq_intCast C a, t2_def, map_C, complexT2_C]

/-- The integer zero polynomial has root norm zero. -/
@[simp] theorem t2_zero : (0 : ℤ[X]).t2 = 0 := by simp [t2_def]

/-- The integer unit polynomial has root norm zero. -/
@[simp] theorem t2_one : (1 : ℤ[X]).t2 = 0 := by simp [t2_def]

/-- The integer root norm is nonnegative. -/
@[simp, grind ←] theorem t2_nonneg (p : ℤ[X]) : 0 ≤ p.t2 := by simp [t2_def]

/-- The integer root norm is unchanged by nonzero scalar multiplication. -/
@[simp] theorem t2_intCast_mul (p : ℤ[X]) {a : ℤ} (ha : a ≠ 0) :
    ((a : ℤ[X]) * p).t2 = p.t2 := by
  have h : (a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr ha
  rw [← eq_intCast C a]
  simp only [t2_def, Polynomial.map_mul, map_C, Int.coe_castRingHom, complexT2_C_mul _ h]

/-- The integer root norm is additive under multiplication of nonzero polynomials. -/
theorem t2_mul {p q : ℤ[X]} (h : p * q ≠ 0) : (p * q).t2 = p.t2 + q.t2 := by
  have hmap : (p * q).map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr h
  rw [Polynomial.map_mul] at hmap
  simpa only [t2_def, Polynomial.map_mul] using complexT2_mul hmap

/-- For a monic complex polynomial of degree `n`, the norm of the coefficient of `X^(n-k)`
is at most `n.choose k * (T₂ / n)^(k/2)` for `k ≤ n`. The monic constant case is included. -/
theorem norm_coeff_le_of_complexT2 {p : ℂ[X]} (hp : p.Monic) {k : ℕ} (hk : k ≤ p.natDegree) :
    ‖p.coeff (p.natDegree - k)‖ ≤
      (p.natDegree.choose k : ℝ) * (p.complexT2 / p.natDegree) ^ ((k : ℝ) / 2) := by
  have hcard := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hv := coeff_eq_esymm_roots_of_card hcard (Nat.sub_le p.natDegree k)
  rw [Nat.sub_sub_self hk, hp.leadingCoeff, one_mul] at hv
  rw [hv, Real.rpow_div_two_eq_sqrt _ (div_nonneg p.complexT2_nonneg (Nat.cast_nonneg _)),
    Real.rpow_natCast, complexT2_def, ← hcard]
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
    p.roots.norm_esymm_le_choose_mul_sqrt_mean_sq_pow k

/-- The coefficient bound in terms of `T₂` for monic integer polynomials. -/
theorem abs_coeff_le_of_t2 {p : ℤ[X]} (hp : p.Monic) {k : ℕ} (hk : k ≤ p.natDegree) :
    |(p.coeff (p.natDegree - k) : ℝ)| ≤
      (p.natDegree.choose k : ℝ) * (p.t2 / p.natDegree) ^ ((k : ℝ) / 2) := by
  have hdeg := hp.natDegree_map (Int.castRingHom ℂ)
  have hbound := norm_coeff_le_of_complexT2 (hp.map (Int.castRingHom ℂ))
    (k := k) (hdeg.symm ▸ hk)
  simpa only [t2_def, hdeg, coeff_map, Int.coe_castRingHom, Complex.norm_intCast] using hbound

-- The root norm uses absolute values: the power sum of the squared roots here would be `-2`.
example : (X ^ 2 + 1 : ℤ[X]).t2 = 2 := by
  have hsq : (C Complex.I : ℂ[X]) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, C_1]
  have hfactor : (X ^ 2 + 1 : ℂ[X]) = (X - C Complex.I) * (X - C (-Complex.I)) := by
    rw [C_neg, sub_neg_eq_add, mul_comm, ← sq_sub_sq, hsq, sub_neg_eq_add]
  rw [t2_def, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one, hfactor,
    complexT2_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp only [complexT2_X_sub_C, norm_neg, Complex.norm_I, one_pow]
  norm_num

end Polynomial
