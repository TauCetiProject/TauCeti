/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.FieldTheory.Minpoly.Primitive

import Mathlib.Analysis.Polynomial.CauchyBound
import TauCeti.Analysis.Polynomial.SupNorm.Basic

/-!
# The naive height of an algebraic number

For an element `x` of a field of characteristic zero, the *naive height* `H(x)` is the largest
absolute value of a coefficient of its primitive minimal polynomial `F_x ∈ ℤ[X]`, that is, the
coefficient sup norm `Polynomial.supNorm` of `F_x`. For transcendental `x` the value is `1`.

Like the Mahler measure, the naive height needs no complex embedding of the ambient field, so it
is invariant under field embeddings and constant on conjugacy classes. It is the size function in
which classical approximation statements are phrased: counting algebraic numbers of bounded
degree and height, Liouville-type lower bounds, and exponents of approximation by algebraic
numbers. It agrees with the
multiplicative height `max(|p|, q)` on a rational number `p / q` in lowest terms, and it controls
the complex absolute values of `x` from both sides.

## Main definitions

* `TauCeti.naiveHeight x`: the naive height of `x`.

## Main results

* `TauCeti.naiveHeight_eq_iSup`: `H(x)` is the supremum of the absolute values of the
  coefficients of `F_x`.
* `TauCeti.leadingCoeff_le_naiveHeight`, `TauCeti.one_le_naiveHeight`: `1 ≤ a₀ ≤ H(x)`, where
  `a₀` is the leading coefficient of `F_x`.
* `TauCeti.naiveHeight_map`, `TauCeti.naiveHeight_eq_of_minpoly_eq`: invariance under field
  embeddings and conjugation.
* `TauCeti.naiveHeight_ratCast`, `TauCeti.naiveHeight_ratCast_eq_mulHeight₁`:
  `H(p/q) = max(|p|, q)`, the multiplicative height of `p / q`.
* `TauCeti.naiveHeight_intCast`: `H(n) = max(|n|, 1)`.
* `TauCeti.naiveHeight_inv`: `H(x⁻¹) = H(x)`.
* `TauCeti.natDenominator_le_naiveHeight`: the denominator of `x` is at most `H(x)`.
* `TauCeti.norm_lt_naiveHeight_add_one`, `TauCeti.inv_naiveHeight_add_one_lt_norm`: for algebraic
  `x` in `ℝ` or `ℂ`, `(H(x) + 1)⁻¹ < |x| < H(x) + 1`, the former for `x ≠ 0`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 3, §3.1 and Exercise 3.1;
  ch. 6, §6.1.
* Y. Bugeaud, *Exponents of Diophantine approximation*, arXiv:1502.03052 (2015), §2,
  Definition 2.1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F] {F' : Type*} [Field F'] [CharZero F']

/-- The *naive height* `H(x)` of `x`: the largest absolute value of a coefficient of the primitive
minimal polynomial `F_x ∈ ℤ[X]`. For transcendental `x` it is `1`
(`naiveHeight_of_not_isAlgebraic`). -/
noncomputable def naiveHeight (x : F) : ℝ :=
  (primitiveMinpoly x).supNorm

/-- The naive height of `x` is the coefficient sup norm of `F_x`. -/
theorem naiveHeight_def (x : F) : naiveHeight x = (primitiveMinpoly x).supNorm := (rfl)

/-- The naive height of `x` is the supremum of the absolute values of the coefficients of
`F_x`. -/
theorem naiveHeight_eq_iSup (x : F) :
    naiveHeight x = ⨆ i, |((primitiveMinpoly x).coeff i : ℝ)| := by
  simp only [naiveHeight_def, supNorm_eq_iSup, Int.norm_eq_abs]

/-- Each coefficient of `F_x` is bounded in absolute value by the naive height of `x`. -/
theorem abs_coeff_primitiveMinpoly_le_naiveHeight (x : F) (i : ℕ) :
    |((primitiveMinpoly x).coeff i : ℝ)| ≤ naiveHeight x := by
  simpa only [naiveHeight_def, Int.norm_eq_abs] using (primitiveMinpoly x).le_supNorm i

/-- The leading coefficient `a₀` of `F_x` is at most the naive height of `x`. -/
theorem leadingCoeff_le_naiveHeight (x : F) :
    ((primitiveMinpoly x).leadingCoeff : ℝ) ≤ naiveHeight x := by
  have h := abs_coeff_primitiveMinpoly_le_naiveHeight x (primitiveMinpoly x).natDegree
  rwa [coeff_natDegree, abs_of_pos (by exact_mod_cast leadingCoeff_primitiveMinpoly_pos x)] at h

/-- The naive height of every element is at least `1`. -/
theorem one_le_naiveHeight (x : F) : 1 ≤ naiveHeight x :=
  le_trans (by exact_mod_cast leadingCoeff_primitiveMinpoly_pos x) (leadingCoeff_le_naiveHeight x)

/-- The naive height depends only on `minpoly ℚ x`: conjugates, possibly lying in different
fields, have the same naive height. -/
theorem naiveHeight_eq_of_minpoly_eq {x : F} {y : F'} (h : minpoly ℚ x = minpoly ℚ y) :
    naiveHeight x = naiveHeight y := by
  rw [naiveHeight_def, naiveHeight_def, primitiveMinpoly_eq_of_minpoly_eq h]

/-- Field embeddings preserve the naive height. -/
@[simp]
theorem naiveHeight_map (f : F →+* F') (x : F) : naiveHeight (f x) = naiveHeight x := by
  rw [naiveHeight_def, naiveHeight_def, primitiveMinpoly_map]

/-- The junk value: `H(x) = 1` for `x` transcendental over `ℚ`. -/
@[simp]
theorem naiveHeight_of_not_isAlgebraic {x : F} (hx : ¬IsAlgebraic ℚ x) : naiveHeight x = 1 := by
  rw [naiveHeight_def, primitiveMinpoly_of_not_isAlgebraic hx, ← C_1, supNorm_C, norm_one]

/-- The naive height of a rational number `q` is the maximum of the absolute value of its
numerator and its denominator, independently of the field containing `q`. -/
@[simp]
theorem naiveHeight_ratCast (q : ℚ) :
    naiveHeight (q : F) = max (q.num.natAbs : ℝ) q.den := by
  rw [naiveHeight_def, primitiveMinpoly_ratCast]
  set P : ℤ[X] := C (q.den : ℤ) * X - C q.num
  have hP (i : ℕ) :
      P.coeff i = (if i = 1 then (q.den : ℤ) else 0) - if i = 0 then q.num else 0 := by
    simp only [P, coeff_sub, coeff_C_mul_X, coeff_C]
  have h0 : ‖P.coeff 0‖ = q.num.natAbs := by simp [hP, Int.norm_eq_abs, Nat.cast_natAbs]
  have h1 : ‖P.coeff 1‖ = q.den := by simp [hP]
  refine le_antisymm ?_ (max_le (h0 ▸ P.le_supNorm 0) (h1 ▸ P.le_supNorm 1))
  obtain ⟨i, hi⟩ := P.exists_eq_supNorm
  rw [hi]
  rcases i with _ | _ | i
  · exact h0.le.trans (le_max_left _ _)
  · exact h1.le.trans (le_max_right _ _)
  · simp [hP]

/-- On rational numbers the naive height is the multiplicative Weil height. -/
theorem naiveHeight_ratCast_eq_mulHeight₁ (q : ℚ) :
    naiveHeight (q : F) = Height.mulHeight₁ q := by
  rw [naiveHeight_ratCast, Rat.mulHeight₁_eq_max, Nat.cast_max]

/-- The naive height of an integer `n` is `max(|n|, 1)`. -/
@[simp]
theorem naiveHeight_intCast (n : ℤ) : naiveHeight (n : F) = max |(n : ℝ)| 1 := by
  simpa [Nat.cast_natAbs] using naiveHeight_ratCast (F := F) n

/-- The naive height of `0` is `1`. -/
@[simp]
theorem naiveHeight_zero : naiveHeight (0 : F) = 1 := by
  simpa using naiveHeight_intCast (F := F) 0

/-- The naive height of `1` is `1`. -/
@[simp]
theorem naiveHeight_one : naiveHeight (1 : F) = 1 := by
  simpa using naiveHeight_intCast (F := F) 1

/-- Inversion preserves the naive height (Evertse, Exercise 3.1(i)). This also holds at `x = 0`,
where `0⁻¹ = 0`. -/
@[simp]
theorem naiveHeight_inv (x : F) : naiveHeight x⁻¹ = naiveHeight x := by
  rw [naiveHeight_def, naiveHeight_def, primitiveMinpoly_inv, normalize_apply, coe_normUnit,
    supNorm_mul_C, supNorm_mirror]
  generalize normUnit (primitiveMinpoly x).mirror.leadingCoeff = u
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- The denominator of `x` is at most its naive height. For algebraic `x` the denominator
divides the leading coefficient of `F_x`; for transcendental `x` it is `0`. -/
theorem natDenominator_le_naiveHeight (x : F) :
    (Algebra.natDenominator x : ℝ) ≤ naiveHeight x := by
  by_cases hx : IsAlgebraic ℚ x
  · have h := Int.le_of_dvd (leadingCoeff_primitiveMinpoly_pos x)
      (natDenominator_dvd_leadingCoeff_primitiveMinpoly hx)
    exact le_trans (by exact_mod_cast h) (leadingCoeff_le_naiveHeight x)
  · have h0 : Algebra.natDenominator x = 0 := by
      by_contra h
      have hd : Algebra.denominator ℤ x ≠ 0 := by
        rw [Algebra.natDenominator_def] at h
        exact Int.natAbs_ne_zero.mp h
      exact hx (((Algebra.isIntegral_denominator_smul x).isAlgebraic.of_smul
        (mem_nonZeroDivisors_of_ne_zero hd)).extendScalars (RingHom.injective_int _))
    rw [h0, Nat.cast_zero]
    exact zero_le_one.trans (one_le_naiveHeight x)

section RCLike

variable {K : Type*} [RCLike K]

/-- An algebraic element of `ℝ` or `ℂ` has absolute value less than `H(x) + 1` (Evertse,
Exercise 3.1(ii)). -/
theorem norm_lt_naiveHeight_add_one {x : K} (hx : IsAlgebraic ℚ x) :
    ‖x‖ < naiveHeight x + 1 := by
  set P := (primitiveMinpoly x).map (Int.castRingHom K)
  have hP : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr (primitiveMinpoly_ne_zero x)
  have hroot : P.IsRoot x := by
    rw [IsRoot, eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_primitiveMinpoly hx]
  have hnorm (n : ℤ) : ‖(n : K)‖ = |(n : ℝ)| := by
    rw [← RCLike.ofReal_intCast, RCLike.norm_ofReal]
  have hlc : 1 ≤ ‖P.leadingCoeff‖ := by
    rw [leadingCoeff_map_of_injective (RingHom.injective_int _), eq_intCast, hnorm,
      abs_of_pos (by exact_mod_cast leadingCoeff_primitiveMinpoly_pos x)]
    exact_mod_cast leadingCoeff_primitiveMinpoly_pos x
  have hH : 0 ≤ naiveHeight x := zero_le_one.trans (one_le_naiveHeight x)
  have hsup : (Finset.range P.natDegree).sup (‖P.coeff ·‖₊) ≤ (naiveHeight x).toNNReal :=
    Finset.sup_le fun i _ ↦ by
      rw [Real.le_toNNReal_iff_coe_le hH, coe_nnnorm, coeff_map, eq_intCast, hnorm]
      exact abs_coeff_primitiveMinpoly_le_naiveHeight x i
  have h := hroot.norm_lt_cauchyBound hP
  rw [← NNReal.coe_lt_coe, coe_nnnorm, cauchyBound, NNReal.coe_add, NNReal.coe_div,
    coe_nnnorm, NNReal.coe_one] at h
  refine h.trans_le (add_le_add_left ?_ 1)
  exact (div_le_self (NNReal.coe_nonneg _) hlc).trans ((Real.le_toNNReal_iff_coe_le hH).mp hsup)

/-- A nonzero algebraic element of `ℝ` or `ℂ` has absolute value greater than `(H(x) + 1)⁻¹`
(Evertse, Exercise 3.1(ii)). -/
theorem inv_naiveHeight_add_one_lt_norm {x : K} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    (naiveHeight x + 1)⁻¹ < ‖x‖ := by
  have h := norm_lt_naiveHeight_add_one (IsAlgebraic.inv_iff.mpr hx)
  rw [naiveHeight_inv, norm_inv] at h
  exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) (by linarith [one_le_naiveHeight x])).mp h

end RCLike

/-! ### Examples -/

/- `H(2/3) = 3`, in every field of characteristic zero. -/
example : naiveHeight (((2 : ℚ) / 3 : ℚ) : F) = 3 := by
  rw [naiveHeight_ratCast, show ((2 : ℚ) / 3).den = 3 by norm_num,
    show ((2 : ℚ) / 3).num = 2 by norm_num]
  norm_num

end TauCeti
