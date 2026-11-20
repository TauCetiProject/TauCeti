/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Minpoly.Primitive
public import TauCeti.Analysis.Polynomial.SupNorm.Roots
public import Mathlib.NumberTheory.Height.NumberField
import TauCeti.Algebra.Field.LinearFractional
import TauCeti.Algebra.Polynomial.Homogenize
import TauCeti.Analysis.Polynomial.L1Norm
import TauCeti.Analysis.Polynomial.SupNorm.Factor
import TauCeti.FieldTheory.IntermediateField.Adjoin.Mobius
import TauCeti.RingTheory.Polynomial.Primitive
import Mathlib.Analysis.Normed.Ring.Int
import TauCeti.Analysis.Polynomial.L1Norm
import TauCeti.Analysis.Polynomial.SupNorm.Factor

/-!
# Naive height of an algebraic number

The naive height is the largest absolute value of a coefficient of the primitive
integer minimal polynomial. It is defined in every characteristic-zero field,
without a chosen complex embedding, and is constant on conjugacy classes.
The value at a transcendental element is one.

For rational numbers it agrees with the multiplicative Weil height. For general
algebraic numbers it instead measures the size of their defining polynomial;
its bounds control denominators and the norms of real or complex roots, Gelfond's
divisor estimate bounds the naive height of any root of a nonzero integer polynomial `P`
by `2 ^ deg P * P.supNorm` (`naiveHeight_le_two_pow_mul_supNorm_of_aeval_eq_zero`), and
its bounds control denominators and the norms of real or complex roots,
`norm_aeval_primitiveMinpoly_le` bounds the primitive minimal polynomial near its
complex roots, and `naiveHeight_mul_add_div_mul_add_le` controls how the naive height
grows under nonsingular integer Möbius transformations.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 3, §3.1,
  Exercise 3.1, and ch. 6, §6.1.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.3.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), ch. 3
  and Appendix A.
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

/-- The natural denominator is at most the naive height. For a transcendental element the
natural denominator is the junk value `0`. -/
theorem natDenominator_le_naiveHeight (x : F) :
    (Algebra.natDenominator x : ℝ) ≤ naiveHeight x := by
  by_cases hx : IsAlgebraic ℚ x
  · have h := Int.le_of_dvd (leadingCoeff_primitiveMinpoly_pos x)
      (natDenominator_dvd_leadingCoeff_primitiveMinpoly hx)
    have h' : (Algebra.natDenominator x : ℝ) ≤ (primitiveMinpoly x).leadingCoeff := by
      exact_mod_cast h
    exact h'.trans (leadingCoeff_primitiveMinpoly_le_naiveHeight x)
  · have h0 : Algebra.natDenominator x = 0 :=
      not_not.1 (mt Algebra.natDenominator_ne_zero_iff_isAlgebraic_rat.1 hx)
    simpa [h0] using zero_le_one.trans (one_le_naiveHeight x)

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
  · have h₁ := primitiveMinpoly_inv_dvd_reverse hx0
    have h₂ : primitiveMinpoly x ∣ (primitiveMinpoly x⁻¹).reverse := by
      simpa only [inv_inv] using primitiveMinpoly_inv_dvd_reverse (inv_ne_zero hx0)
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

/-- Near a complex algebraic number `α` of degree `d`, its primitive minimal polynomial `F_α` is
small: `|F_α(z)| ≤ (d + 1) (2 + |z|) ^ d H(α) |z - α|`, where `H(α)` is the naive height of `α`.
The bound is only informative when `|z - α| ≤ 1`, but holds for every `z`. -/
theorem norm_aeval_primitiveMinpoly_le {α z : ℂ} (hα : IsAlgebraic ℚ α) :
    ‖aeval z (primitiveMinpoly α)‖ ≤ ((minpoly ℚ α).natDegree + 1) *
      (2 + ‖z‖) ^ (minpoly ℚ α).natDegree * naiveHeight α * ‖z - α‖ := by
  set d := (minpoly ℚ α).natDegree
  set P := (primitiveMinpoly α).map (Int.castRingHom ℂ)
  have hroot : P.IsRoot α := by
    simpa [P, IsRoot, eval_map, aeval_def] using aeval_primitiveMinpoly hα
  -- Dividing out the root `α` writes `F_α(z) = V(z) (z - α)`.
  have hV : P /ₘ (X - C α) * (X - C α) ^ 1 = P := by
    rw [pow_one, mul_comm]
    exact mul_divByMonic_eq_iff_isRoot.2 hroot
  have hPz : aeval z (primitiveMinpoly α) = P.eval z := by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
  have heval : aeval z (primitiveMinpoly α) = (P /ₘ (X - C α)).eval z * (z - α) := by
    rw [hPz]
    conv_lhs => rw [← hV]
    simp
  have hdeg : P.natDegree ≤ d := natDegree_map_le.trans (natDegree_primitiveMinpoly α).le
  have hl1 : P.l1Norm ≤ (d + 1) * naiveHeight α := by
    rw [l1Norm_map _ _ fun x ↦ by simp [Int.norm_eq_abs]]
    refine ((primitiveMinpoly α).l1Norm_le_natDegree_add_one_mul_supNorm).trans ?_
    rw [naiveHeight_def, natDegree_primitiveMinpoly]
  have hH : 0 ≤ (d + 1 : ℝ) * naiveHeight α :=
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_naiveHeight α))
  -- Any `t ≤ 2 + ‖z‖` raised to the degree of `P` is at most `(2 + ‖z‖) ^ d`.
  have hpow : ∀ t : ℝ, 0 ≤ t → t ≤ 2 + ‖z‖ → t ^ P.natDegree ≤ (2 + ‖z‖) ^ d := fun t ht ht' ↦
    (pow_le_pow_left₀ ht ht' _).trans (pow_le_pow_right₀ (by linarith [norm_nonneg z]) hdeg)
  rcases le_or_gt ‖z - α‖ 1 with hz | hz
  · have hα₁ : 1 + ‖α‖ ≤ 2 + ‖z‖ := by
      have := norm_le_norm_add_norm_sub' α z
      rw [norm_sub_rev] at this
      linarith
    calc ‖aeval z (primitiveMinpoly α)‖ = ‖(P /ₘ (X - C α)).eval z‖ * ‖z - α‖ := by
          rw [heval, norm_mul]
      _ ≤ P.l1Norm * (1 + ‖α‖) ^ P.natDegree * ‖z - α‖ := by
          gcongr
          exact norm_eval_le_l1Norm_mul_of_mul_X_sub_C_pow_eq hV hz
      _ ≤ (d + 1) * naiveHeight α * (2 + ‖z‖) ^ d * ‖z - α‖ := by
          gcongr
          exact hpow _ (by positivity) hα₁
      _ = (d + 1) * (2 + ‖z‖) ^ d * naiveHeight α * ‖z - α‖ := by ring
  · -- Far from `α`, bound `F_α(z)` directly and absorb the factor `‖z - α‖ > 1`.
    calc ‖aeval z (primitiveMinpoly α)‖ = ‖P.eval z‖ := by rw [hPz]
      _ ≤ P.l1Norm * max 1 ‖z‖ ^ P.natDegree := norm_eval_le_l1Norm_mul P z
      _ ≤ (d + 1) * naiveHeight α * (2 + ‖z‖) ^ d := by
          have hm : max 1 ‖z‖ ≤ 2 + ‖z‖ :=
            max_le (by linarith [norm_nonneg z]) (by linarith [norm_nonneg z])
          exact mul_le_mul hl1 (hpow _ (by positivity) hm) (by positivity) hH
      _ ≤ (d + 1) * naiveHeight α * (2 + ‖z‖) ^ d * ‖z - α‖ :=
          le_mul_of_one_le_right (by positivity) hz.le
      _ = (d + 1) * (2 + ‖z‖) ^ d * naiveHeight α * ‖z - α‖ := by ring

/-- If a nonzero integer polynomial `P` vanishes at `x`, then the naive height of `x` is at most
`2 ^ P.natDegree * P.supNorm`, by Gelfond's factor bound applied to `primitiveMinpoly x ∣ P`. -/
theorem naiveHeight_le_two_pow_mul_supNorm_of_aeval_eq_zero {x : F} {P : ℤ[X]} (hP : P ≠ 0)
    (hx : aeval x P = 0) :
    naiveHeight x ≤ 2 ^ P.natDegree * P.supNorm := by
  rw [naiveHeight_def]
  exact supNorm_le_two_pow_mul_supNorm_of_dvd_int
    ((primitiveMinpoly_dvd_iff (isAlgebraic_rat_of_aeval_eq_zero hP hx)).2 hx) hP

/-- **Naive height under an integer Möbius transformation.** For any `x` in a field of
characteristic zero and integers `a, b, c, d` with `a * d - b * c ≠ 0`,
`H((a x + b) / (c x + d)) ≤ (2 (|a| + |b| + |c| + |d|)) ^ deg(x) H(x)`. The bound holds at
transcendental elements (where `deg(x) = 0` and both heights are `1`) and at the pole
`c x + d = 0` (where the left-hand side is `H(0) = 1`). -/
theorem naiveHeight_mul_add_div_mul_add_le (x : F) {a b c d : ℤ} (hdet : a * d - b * c ≠ 0) :
    naiveHeight (((a : F) * x + b) / ((c : F) * x + d)) ≤
      (2 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + |(d : ℝ)|)) ^ (minpoly ℚ x).natDegree *
        naiveHeight x := by
  set y : F := ((a : F) * x + b) / ((c : F) * x + d)
  set S : ℝ := |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + |(d : ℝ)|
  by_cases hpole : (c : F) * x + d = 0
  · have hab : (1 : ℤ) ≤ |a| + |b| := by
      rcases eq_or_ne a 0 with rfl | ha
      · simpa using Int.one_le_abs (fun hb ↦ hdet (by simp [hb]))
      · linarith [Int.one_le_abs ha, abs_nonneg b]
    have habR : (1 : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| := by exact_mod_cast hab
    simp only [y, hpole, div_zero, naiveHeight_zero]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by linarith [abs_nonneg (c : ℝ), abs_nonneg (d : ℝ)])) (one_le_naiveHeight x)
  have hdetQ : (a : ℚ) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have halg_iff : IsAlgebraic ℚ y ↔ IsAlgebraic ℚ x := by
    simpa [y] using isAlgebraic_mul_add_div_mul_add_iff (K := ℚ) x hdetQ
  by_cases hx : IsAlgebraic ℚ x
  swap
  · rw [naiveHeight_of_not_isAlgebraic (mt halg_iff.mp hx), naiveHeight_of_not_isAlgebraic hx,
      minpoly.eq_zero (isAlgebraic_iff_isIntegral.not.mp hx), natDegree_zero, pow_zero, one_mul]
  set P : ℤ[X] := primitiveMinpoly x
  set g₁ : ℤ[X] := C d * X + C (-b)
  set g₂ : ℤ[X] := C (-c) * X + C a
  set Q : ℤ[X] := MvPolynomial.aeval ![g₁, g₂] (P.homogenize P.natDegree)
  have hdet' : d * a - (-b) * (-c) ≠ 0 := fun h0 ↦ hdet (by linear_combination h0)
  have hQ0 : Q ≠ 0 := aeval_linear_homogenize_ne_zero (primitiveMinpoly_ne_zero x) le_rfl hdet'
  have hdetF : (a : F) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have hyQ : aeval y Q = 0 := by
    rw [MvPolynomial.comp_aeval_apply, aeval_homogenize le_rfl _
      (by simpa [g₂] using neg_mul_moebius_add_ne_zero hdetF hpole)]
    have hdiv : aeval y g₁ / aeval y g₂ = x := by
      simpa [g₁, g₂, sub_eq_add_neg] using moebius_inv_moebius hdetF hpole
    simp [P, hdiv, aeval_primitiveMinpoly hx]
  have hdvd : primitiveMinpoly y ∣ Q := (primitiveMinpoly_dvd_iff (halg_iff.mpr hx)).mpr hyQ
  have hQdeg : Q.natDegree ≤ P.natDegree := (isHomogeneous_homogenize P).natDegree_aeval_le
    fun i ↦ by fin_cases i <;> exact natDegree_linear_le
  have hg : g₁.l1Norm + g₂.l1Norm ≤ S := by
    have h₁ := l1Norm_C_mul_X_add_C_le d (-b)
    have h₂ := l1Norm_C_mul_X_add_C_le (-c) a
    simp only [Int.norm_eq_abs, Int.cast_neg, abs_neg] at h₁ h₂
    linarith
  have hQsup : Q.supNorm ≤ P.supNorm * S ^ P.natDegree :=
    ((supNorm_le_l1Norm Q).trans (l1Norm_aeval_homogenize_le P P.natDegree g₁ g₂)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg g₁.l1Norm_nonneg g₂.l1Norm_nonneg) hg _) P.supNorm_nonneg)
  calc naiveHeight y = (primitiveMinpoly y).supNorm := naiveHeight_def y
    _ ≤ 2 ^ Q.natDegree * Q.supNorm := supNorm_le_two_pow_mul_supNorm_of_dvd hdvd hQ0
    _ ≤ 2 ^ P.natDegree * (P.supNorm * S ^ P.natDegree) :=
        mul_le_mul (pow_le_pow_right₀ one_le_two hQdeg) hQsup Q.supNorm_nonneg (by positivity)
    _ = (2 * S) ^ (minpoly ℚ x).natDegree * naiveHeight x := by
        rw [← natDegree_primitiveMinpoly x, ← naiveHeight_def x, mul_pow]; ring

end TauCeti
