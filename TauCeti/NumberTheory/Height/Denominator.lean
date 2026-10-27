/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Minpoly.Primitive
public import TauCeti.NumberTheory.Height.House
public import TauCeti.RingTheory.Algebraic.Denominator

import Mathlib.Topology.Algebra.Polynomial

/-!
# Denominators and the size of an algebraic number

The *denominator* `den(x) = Algebra.natDenominator x` of an algebraic number `x` is the least
positive integer `D` such that `D x` is an algebraic integer: it generates the ideal of integers
clearing the denominator of `x` (`Algebra.natDenominator_dvd_iff`), and it is `1` exactly for an
algebraic integer (`Algebra.natDenominator_eq_one_iff`). It divides the leading coefficient of the
primitive minimal polynomial of `x`
(`TauCeti.natDenominator_dvd_leadingCoeff_primitiveMinpoly`), which is at most its `d`-th power
(`TauCeti.leadingCoeff_primitiveMinpoly_le_natDenominator_pow`).

The main result is Evertse's lower bound for the conjugates of a nonzero algebraic number: for an
algebraic `z` of degree `d` over `ℚ` in a field of characteristic zero and every complex conjugate
`w` of `z`,

  `den(z) ^ d * house(z) ^ (d - 1) * ‖w‖ ≥ 1`,

that is, `‖w‖ ≥ den(z) ^ (-d) * house(z) ^ (1 - d)`
(`TauCeti.one_le_natDenominator_pow_mul_house_pow_mul_norm_of_mem_rootSet`); the form with integer
powers is stated at `w = z` (`TauCeti.zpow_natDenominator_mul_zpow_house_le_norm`). The leading
coefficient of the primitive minimal polynomial satisfies the sharper bound
`TauCeti.one_le_leadingCoeff_primitiveMinpoly_mul_house_pow_mul_norm`. For an algebraic integer
the denominator is `1`, so the bound reads `house(z) ^ (d - 1) * ‖w‖ ≥ 1` for every conjugate `w`
(`TauCeti.one_le_house_pow_mul_norm_of_mem_rootSet`).

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 3, Exercise 3.7, p. 60.
-/

public section

open Polynomial

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K]

/-- **The conjugate bound in terms of the leading coefficient.** Let `z` be a nonzero algebraic
number of degree `d` in a field of characteristic zero and let `a₀` be the leading coefficient of
its primitive minimal polynomial. Every complex conjugate `w` of `z` satisfies
`a₀ * house(z) ^ (d - 1) * ‖w‖ ≥ 1`. -/
theorem one_le_leadingCoeff_primitiveMinpoly_mul_house_pow_mul_norm {z : K} {w : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) (hw : w ∈ (minpoly ℚ z).rootSet ℂ) :
    1 ≤ ((primitiveMinpoly z).leadingCoeff : ℝ) * house z ^ ((minpoly ℚ z).natDegree - 1) *
      ‖w‖ := by
  have hint : IsIntegral ℚ z := hz.isIntegral
  have hmono : (minpoly ℚ z).Monic := minpoly.monic hint
  set P : ℂ[X] := (minpoly ℚ z).map (algebraMap ℚ ℂ) with hP
  have hPmono : P.Monic := hmono.map _
  have hP0 : P ≠ 0 := hPmono.ne_zero
  have hwroot : P.IsRoot w := by
    have hw' := (mem_rootSet_of_ne (minpoly.ne_zero hint)).mp hw
    simpa [hP, Polynomial.IsRoot, eval_map, aeval_def] using hw'
  -- divide the minimal polynomial by the linear factor at the conjugate `w`
  set q : ℂ[X] := P /ₘ (X - C w)
  have hfac : (X - C w) * q = P := mul_divByMonic_eq_iff_isRoot.mpr hwroot
  have hqmono : q.Monic := by
    have h := congrArg leadingCoeff hfac
    rw [leadingCoeff_mul, (monic_X_sub_C w).leadingCoeff, one_mul, hPmono.leadingCoeff] at h
    exact h
  have hq0 : q ≠ 0 := hqmono.ne_zero
  have hqdeg : q.natDegree = (minpoly ℚ z).natDegree - 1 := by
    have h := congrArg natDegree hfac
    rw [natDegree_mul (monic_X_sub_C w).ne_zero hq0, natDegree_X_sub_C, hP,
      natDegree_map_eq_of_injective (RingHom.injective (algebraMap ℚ ℂ))] at h
    omega
  -- the remaining roots of the quotient are the other conjugates of `z`
  have hroot_le : ∀ u ∈ q.roots, ‖u‖ ≤ house z := by
    intro u hu
    have huP : P.IsRoot u := by
      rw [Polynomial.IsRoot.def, ← hfac, eval_mul, eval_sub, eval_X, eval_C]
      exact mul_eq_zero_of_right _ ((mem_roots hq0).mp hu)
    refine norm_le_house_of_mem_rootSet ?_
    rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, ← hP]
    exact (mem_roots hP0).mpr huP
  have hqcoeff : ‖q.coeff 0‖ ≤ house z ^ ((minpoly ℚ z).natDegree - 1) := by
    have h := coeff_le_of_roots_le (p := q) (f := RingHom.id ℂ) (B := house z) 0 hqmono
      (IsAlgClosed.splits _) (by simpa using hroot_le)
    simpa only [Polynomial.map_id, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      hqdeg] using h
  -- the constant term of the minimal polynomial is `-w` times that of the quotient
  have hconst : P.coeff 0 = -w * q.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, ← hfac, eval_mul, eval_sub, eval_X, eval_C, zero_sub,
      coeff_zero_eq_eval_zero]
  have hcoeff0 : (primitiveMinpoly z).coeff 0 ≠ 0 := coeff_zero_primitiveMinpoly_ne_zero hz hz0
  -- the constant term of `F_z` is a nonzero integer, so it has modulus at least `1`
  have hint_norm : (1 : ℝ) ≤ ‖((primitiveMinpoly z).coeff 0 : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hcoeff0
  have hcast : ((primitiveMinpoly z).coeff 0 : ℂ) =
      ((primitiveMinpoly z).leadingCoeff : ℂ) * P.coeff 0 := by
    have h1 := congrArg (fun p : ℚ[X] => p.coeff 0) (map_primitiveMinpoly hz)
    simp only [coeff_map, Int.coe_castRingHom, coeff_C_mul] at h1
    have h2 := congrArg (fun q : ℚ => (q : ℂ)) h1
    push_cast at h2
    have h3 : P.coeff 0 = ((minpoly ℚ z).coeff 0 : ℂ) := by
      rw [hP, coeff_map]
      norm_num
    rw [h3]
    exact h2
  have hnorm_a : ‖((primitiveMinpoly z).leadingCoeff : ℂ)‖ =
      ((primitiveMinpoly z).leadingCoeff : ℝ) := by
    rw [Complex.norm_intCast, abs_of_pos]
    exact_mod_cast leadingCoeff_primitiveMinpoly_pos z
  calc (1 : ℝ) ≤ ‖((primitiveMinpoly z).coeff 0 : ℂ)‖ := hint_norm
    _ = ((primitiveMinpoly z).leadingCoeff : ℝ) * ‖P.coeff 0‖ := by
        rw [hcast, norm_mul, hnorm_a]
    _ = ((primitiveMinpoly z).leadingCoeff : ℝ) * (‖w‖ * ‖q.coeff 0‖) := by
        rw [hconst, norm_mul, norm_neg]
    _ ≤ ((primitiveMinpoly z).leadingCoeff : ℝ) *
          (‖w‖ * house z ^ ((minpoly ℚ z).natDegree - 1)) := by
        have ha : (0 : ℝ) ≤ ((primitiveMinpoly z).leadingCoeff : ℝ) := by
          exact_mod_cast (leadingCoeff_primitiveMinpoly_pos z).le
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hqcoeff (norm_nonneg w)) ha
    _ = ((primitiveMinpoly z).leadingCoeff : ℝ) * house z ^ ((minpoly ℚ z).natDegree - 1) *
          ‖w‖ := by ring

/-- **Evertse's lower bound for the conjugates of an algebraic number.** Let `z` be a nonzero
algebraic number of degree `d` in a field of characteristic zero and `w` a complex conjugate of
`z`. Then `den(z) ^ d * house(z) ^ (d - 1) * ‖w‖ ≥ 1`. -/
theorem one_le_natDenominator_pow_mul_house_pow_mul_norm_of_mem_rootSet {z : K} {w : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) (hw : w ∈ (minpoly ℚ z).rootSet ℂ) :
    1 ≤ (Algebra.natDenominator z : ℝ) ^ (minpoly ℚ z).natDegree *
      house z ^ ((minpoly ℚ z).natDegree - 1) * ‖w‖ := by
  have h := one_le_leadingCoeff_primitiveMinpoly_mul_house_pow_mul_norm hz hz0 hw
  have hD : ((primitiveMinpoly z).leadingCoeff : ℝ) ≤
      (Algebra.natDenominator z : ℝ) ^ (minpoly ℚ z).natDegree := by
    have hZ := leadingCoeff_primitiveMinpoly_le_natDenominator_pow hz
    have hcast : ((primitiveMinpoly z).leadingCoeff : ℝ) ≤
        ((Algebra.natDenominator z : ℤ) : ℝ) ^ (minpoly ℚ z).natDegree := by
      exact_mod_cast hZ
    simpa using hcast
  calc (1 : ℝ) ≤ ((primitiveMinpoly z).leadingCoeff : ℝ) *
        house z ^ ((minpoly ℚ z).natDegree - 1) * ‖w‖ := h
    _ ≤ (Algebra.natDenominator z : ℝ) ^ (minpoly ℚ z).natDegree *
          house z ^ ((minpoly ℚ z).natDegree - 1) * ‖w‖ := by
        have hH : (0 : ℝ) ≤ house z ^ ((minpoly ℚ z).natDegree - 1) :=
          pow_nonneg (house_nonneg z) _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hH) (norm_nonneg w)

/-- **Evertse's lower bound.** A nonzero algebraic number `z ∈ ℂ` of degree `d` satisfies
`den(z) ^ d * house(z) ^ (d - 1) * ‖z‖ ≥ 1`. -/
theorem one_le_natDenominator_pow_mul_house_pow_mul_norm {z : ℂ} (hz : IsAlgebraic ℚ z)
    (hz0 : z ≠ 0) :
    1 ≤ (Algebra.natDenominator z : ℝ) ^ (minpoly ℚ z).natDegree *
      house z ^ ((minpoly ℚ z).natDegree - 1) * ‖z‖ :=
  one_le_natDenominator_pow_mul_house_pow_mul_norm_of_mem_rootSet hz hz0
    ((mem_rootSet_of_ne (minpoly.ne_zero hz.isIntegral)).mpr (minpoly.aeval ℚ z))

/-- The lower bound for a nonzero algebraic number of degree `d` as an inequality between
negative and positive integer powers: `den(z) ^ (-d) * house(z) ^ (1 - d) ≤ ‖z‖`. -/
theorem zpow_natDenominator_mul_zpow_house_le_norm {z : ℂ} (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    (Algebra.natDenominator z : ℝ) ^ (-((minpoly ℚ z).natDegree : ℤ)) *
      house z ^ (1 - ((minpoly ℚ z).natDegree : ℤ)) ≤ ‖z‖ := by
  set d := (minpoly ℚ z).natDegree
  have hd1 : 1 ≤ d := minpoly.natDegree_pos hz.isIntegral
  have hDne : Algebra.natDenominator z ≠ 0 :=
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 hz)
  have hD : (0 : ℝ) < (Algebra.natDenominator z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hDne
  have hh : (0 : ℝ) < house z :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz0) (norm_le_house hz)
  have hpow : (0 : ℝ) < (Algebra.natDenominator z : ℝ) ^ d * house z ^ (d - 1) := by
    positivity
  have hzpow : (Algebra.natDenominator z : ℝ) ^ (-(d : ℤ)) * house z ^ (1 - (d : ℤ)) =
      ((Algebra.natDenominator z : ℝ) ^ d * house z ^ (d - 1))⁻¹ := by
    have h2 : (1 : ℤ) - (d : ℤ) = -(((d - 1 : ℕ)) : ℤ) := by omega
    rw [h2, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_inv]
  rw [hzpow, inv_le_iff_one_le_mul₀ hpow]
  calc (1 : ℝ) ≤ (Algebra.natDenominator z : ℝ) ^ d * house z ^ (d - 1) * ‖z‖ :=
        one_le_natDenominator_pow_mul_house_pow_mul_norm hz hz0
    _ = ‖z‖ * ((Algebra.natDenominator z : ℝ) ^ d * house z ^ (d - 1)) := by ring

/-- **The bound for algebraic integers.** A nonzero algebraic integer `z` of degree `d` in a field
of characteristic zero satisfies `house(z) ^ (d - 1) * ‖w‖ ≥ 1` for every complex conjugate `w`
of `z`: its denominator is `1`. -/
theorem one_le_house_pow_mul_norm_of_mem_rootSet {z : K} {w : ℂ} (hz : IsIntegral ℤ z)
    (hz0 : z ≠ 0) (hw : w ∈ (minpoly ℚ z).rootSet ℂ) :
    1 ≤ house z ^ ((minpoly ℚ z).natDegree - 1) * ‖w‖ := by
  have hzQ : IsAlgebraic ℚ z := (hz.tower_top (A := ℚ)).isAlgebraic
  have h := one_le_natDenominator_pow_mul_house_pow_mul_norm_of_mem_rootSet hzQ hz0 hw
  have hD : Algebra.natDenominator z = 1 := Algebra.natDenominator_eq_one_iff.mpr hz
  simpa [hD] using h

/-- **The bound for algebraic integers.** A nonzero algebraic integer `z ∈ ℂ` of degree `d`
satisfies `house(z) ^ (d - 1) * ‖z‖ ≥ 1`: its denominator is `1`. -/
theorem one_le_house_pow_mul_norm {z : ℂ} (hz : IsIntegral ℤ z) (hz0 : z ≠ 0) :
    1 ≤ house z ^ ((minpoly ℚ z).natDegree - 1) * ‖z‖ :=
  one_le_house_pow_mul_norm_of_mem_rootSet hz hz0
    ((mem_rootSet_of_ne (minpoly.ne_zero (hz.tower_top (A := ℚ)))).mpr (minpoly.aeval ℚ z))

/-! ### Examples -/

/- The hypothesis `z ≠ 0` cannot be dropped: at `z = 0` the left-hand side of the bound is `0`. -/
example : ¬(1 ≤ (Algebra.natDenominator (0 : ℂ) : ℝ) ^ (minpoly ℚ (0 : ℂ)).natDegree *
    house (0 : ℂ) ^ ((minpoly ℚ (0 : ℂ)).natDegree - 1) * ‖(0 : ℂ)‖) := by
  simp

end TauCeti
