/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Minpoly.Primitive
public import TauCeti.Analysis.Polynomial.SupNorm.Roots
public import Mathlib.NumberTheory.Height.NumberField
import TauCeti.RingTheory.Polynomial.Primitive
import Mathlib.Analysis.Normed.Ring.Int

/-!
# Naive height of an algebraic number

The naive height is the largest absolute value of a coefficient of the primitive
integer minimal polynomial. It is defined in every characteristic-zero field,
without a chosen complex embedding, and is constant on conjugacy classes.
The value at a transcendental element is one.

For rational numbers it agrees with the multiplicative Weil height. For general
algebraic numbers it instead measures the size of their defining polynomial;
its bounds control denominators and the norms of real or complex roots.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 3, §3.1,
  Exercise 3.1, and ch. 6, §6.1.
-/

public section

open Polynomial

namespace TauCeti

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']

/-- The coefficient sup norm of the primitive integer minimal polynomial.
Its value at a transcendental element is one. -/
noncomputable def naiveHeight (x : F) : ℝ :=
  (primitiveMinpoly x).supNorm

/-- Naive height is the native coefficient sup norm of the primitive minimal polynomial. -/
theorem naiveHeight_def (x : F) : naiveHeight x = (primitiveMinpoly x).supNorm := (rfl)

/-- The naive height is the supremum of the absolute values of the coefficients. -/
theorem naiveHeight_eq_iSup (x : F) :
    naiveHeight x = ⨆ i, ‖(primitiveMinpoly x).coeff i‖ :=
  Polynomial.supNorm_eq_iSup _

/-- Conjugates, even in different ambient fields, have equal naive height. -/
theorem naiveHeight_eq_of_minpoly_eq {x : F} {y : F'}
    (h : minpoly ℚ x = minpoly ℚ y) : naiveHeight x = naiveHeight y := by
  simp only [naiveHeight, primitiveMinpoly_eq_of_minpoly_eq h]

/-- Field embeddings preserve naive height. -/
@[simp]
theorem naiveHeight_map (f : F →+* F') (x : F) : naiveHeight (f x) = naiveHeight x := by
  simp [naiveHeight]

/-- Transcendental elements have naive height one. -/
@[simp]
theorem naiveHeight_of_not_isAlgebraic {x : F} (hx : ¬IsAlgebraic ℚ x) :
    naiveHeight x = 1 := by
  rw [naiveHeight, primitiveMinpoly_of_not_isAlgebraic hx, ← Polynomial.C_1, supNorm_C]
  exact norm_one

/-- The naive height bounds each coefficient of the primitive minimal polynomial. -/
theorem norm_coeff_primitiveMinpoly_le_naiveHeight (x : F) (i : ℕ) :
    ‖(primitiveMinpoly x).coeff i‖ ≤ naiveHeight x :=
  Polynomial.le_supNorm _ _

/-- The positive leading coefficient is bounded by the naive height. -/
theorem leadingCoeff_primitiveMinpoly_le_naiveHeight (x : F) :
    ((primitiveMinpoly x).leadingCoeff : ℝ) ≤ naiveHeight x := by
  have h : (0 : ℝ) < (primitiveMinpoly x).leadingCoeff := by
    exact_mod_cast leadingCoeff_primitiveMinpoly_pos x
  simpa only [Polynomial.coeff_natDegree, Int.norm_eq_abs, abs_of_pos h] using
    norm_coeff_primitiveMinpoly_le_naiveHeight x (primitiveMinpoly x).natDegree

/-- Naive height is at least one, including at transcendental elements. -/
theorem one_le_naiveHeight (x : F) : 1 ≤ naiveHeight x := by
  have h : (1 : ℝ) ≤ (primitiveMinpoly x).leadingCoeff := by
    have := leadingCoeff_primitiveMinpoly_pos x
    exact_mod_cast (by omega : (1 : ℤ) ≤ (primitiveMinpoly x).leadingCoeff)
  exact h.trans (leadingCoeff_primitiveMinpoly_le_naiveHeight x)

/-- For algebraic elements, the natural denominator is at most the naive height. -/
theorem natDenominator_le_naiveHeight {x : F} (hx : IsAlgebraic ℚ x) :
    (Algebra.natDenominator x : ℝ) ≤ naiveHeight x := by
  have h := Int.le_of_dvd (leadingCoeff_primitiveMinpoly_pos x)
    (natDenominator_dvd_leadingCoeff_primitiveMinpoly hx)
  have h' : (Algebra.natDenominator x : ℝ) ≤ (primitiveMinpoly x).leadingCoeff := by
    exact_mod_cast h
  exact h'.trans (leadingCoeff_primitiveMinpoly_le_naiveHeight x)

/-- The naive height of a rational number is the maximum of its numerator's
absolute value and its positive denominator, independently of the ambient field. -/
@[simp]
theorem naiveHeight_ratCast (q : ℚ) :
    naiveHeight (q : F) = max (q.num.natAbs : ℝ) (q.den : ℝ) := by
  rw [naiveHeight, primitiveMinpoly_ratCast]
  let p : ℤ[X] := C (q.den : ℤ) * X - C q.num
  have h0 : p.coeff 0 = -q.num := by simp [p]
  have h1 : p.coeff 1 = q.den := by
    simp only [p, coeff_sub, coeff_C_mul_X, coeff_C]
    norm_num
  have hn : ‖q.num‖ = (q.num.natAbs : ℝ) := by simp [Int.norm_eq_abs]
  have hc (i : ℕ) : ‖p.coeff i‖ ≤ max (q.num.natAbs : ℝ) (q.den : ℝ) := by
    rcases i with _ | _ | i
    · rw [h0, norm_neg, hn]; exact le_max_left _ _
    · rw [h1, Int.norm_natCast]; exact le_max_right _ _
    · have hz : p.coeff (i + 1 + 1) = 0 := by
        simp only [p, coeff_sub, coeff_C_mul_X, coeff_C,
          ite_eq_right (by omega : i + 1 + 1 ≠ 1),
          ite_eq_right (by omega : i + 1 + 1 ≠ 0), sub_self]
      rw [hz, norm_zero]
      exact le_trans (Nat.cast_nonneg _) (le_max_right _ _)
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  refine le_antisymm (hi ▸ hc i) (max_le ?_ ?_)
  · simpa only [h0, norm_neg, hn] using p.le_supNorm 0
  · simpa only [h1, Int.norm_natCast] using p.le_supNorm 1

/-- On rational numbers naive height agrees with the multiplicative Weil height. -/
theorem naiveHeight_ratCast_eq_mulHeight₁ (q : ℚ) :
    naiveHeight (q : F) = Height.mulHeight₁ q := by
  rw [naiveHeight_ratCast, Rat.mulHeight₁_eq_max, Nat.cast_max]

/-- The naive height of an integer is the maximum of its modulus and one. -/
@[simp]
theorem naiveHeight_intCast (n : ℤ) : naiveHeight (n : F) = max (|(n : ℝ)|) 1 := by
  simpa using (naiveHeight_ratCast (F := F) (n : ℚ))

@[simp]
theorem naiveHeight_zero : naiveHeight (0 : F) = 1 := by
  simpa using (naiveHeight_intCast (F := F) 0)

@[simp]
theorem naiveHeight_one : naiveHeight (1 : F) = 1 := by
  simpa using (naiveHeight_intCast (F := F) 1)

/-- Inversion preserves naive height, also at zero and at transcendental elements. -/
@[simp]
theorem naiveHeight_inv (x : F) : naiveHeight x⁻¹ = naiveHeight x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hx : IsAlgebraic ℚ x
  · have h₁ := primitiveMinpoly_inv_dvd_reverse hx hx0
    have h₂ : primitiveMinpoly x ∣ (primitiveMinpoly x⁻¹).reverse := by
      simpa only [inv_inv] using primitiveMinpoly_inv_dvd_reverse hx.inv (inv_ne_zero hx0)
    -- The two divisibilities force equal degrees, so the quotient is a constant unit.
    have hdeg : (primitiveMinpoly x).reverse.natDegree ≤ (primitiveMinpoly x⁻¹).natDegree :=
      (reverse_natDegree_le _).trans ((natDegree_le_of_dvd h₂
        (reverse_eq_zero.not.mpr (primitiveMinpoly_ne_zero _))).trans (reverse_natDegree_le _))
    obtain ⟨u, hu⟩ := ((Polynomial.isPrimitive_reverse_iff _).mpr
      (isPrimitive_primitiveMinpoly x)).exists_eq_mul_C_unit_of_dvd_of_natDegree_le h₁ hdeg
    have h := congrArg Polynomial.supNorm hu
    simpa only [supNorm_reverse, supNorm_mul_C, Int.norm_coe_units, mul_one, naiveHeight]
      using h.symm
  · rw [naiveHeight_of_not_isAlgebraic hx,
      naiveHeight_of_not_isAlgebraic (fun h ↦ hx (by simpa only [inv_inv] using h.inv))]

/-- The norm of a real or complex algebraic number is bounded by its naive height plus one. -/
theorem norm_le_naiveHeight_add_one {K : Type*} [RCLike K] {x : K} (hx : IsAlgebraic ℚ x) :
    ‖x‖ ≤ naiveHeight x + 1 :=
  ((primitiveMinpoly x).norm_lt_supNorm_add_one_of_aeval_eq_zero
    (primitiveMinpoly_ne_zero x) (aeval_primitiveMinpoly hx)).le

/-- A nonzero real or complex algebraic number is bounded away from zero by its naive height. -/
theorem inv_naiveHeight_add_one_le_norm {K : Type*} [RCLike K] {x : K}
    (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    (naiveHeight x + 1)⁻¹ ≤ ‖x‖ :=
  ((primitiveMinpoly x).inv_supNorm_add_one_lt_norm_of_aeval_eq_zero
    (primitiveMinpoly_ne_zero x) (aeval_primitiveMinpoly hx) hx0).le

end TauCeti
