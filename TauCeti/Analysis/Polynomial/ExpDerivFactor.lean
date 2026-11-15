/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Algebra.Polynomial.ExpDerivFactor
import Mathlib.Algebra.Polynomial.Eval.Degree
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Ultrametric coefficient and value bounds for `Polynomial.expDerivFactor`

Over an ultrametric seminormed commutative ring `K`, natural-number multiples satisfy
`‖n • a‖ ≤ ‖a‖`, so formal differentiation shifts polynomial coefficients down by one degree
without introducing factorial growth. Consequently, if `‖P.coeff i‖ * r ^ i ≤ B` for some `r > 0`,
each application of `D + c` multiplies this weighted bound by at most `max r⁻¹ ‖c‖`
(`Polynomial.norm_coeff_expDerivFactor_mul_pow_le`). Specializing to `r = 1` shows that uniform
coefficient bounds grow by at most `max 1 ‖c‖ ^ m` (`Polynomial.norm_coeff_expDerivFactor_le`).

## Main results

* `Polynomial.norm_coeff_expDerivFactor_mul_pow_le`: if `0 < r` and `∀ i, ‖P.coeff i‖ * r ^ i ≤ B`,
  then `‖(expDerivFactor c m P).coeff i‖ * r ^ i ≤ max r⁻¹ ‖c‖ ^ m * B`.
* `Polynomial.norm_coeff_expDerivFactor_le`: if `∀ i, ‖P.coeff i‖ ≤ B`, then
  `‖(expDerivFactor c m P).coeff i‖ ≤ max 1 ‖c‖ ^ m * B`.
* `Polynomial.norm_eval_expDerivFactor_le_of_mul_pow_le`, `Polynomial.norm_eval_expDerivFactor_le`:
  corresponding ultrametric bounds for `(expDerivFactor c m P).eval x` on closed balls.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* M. Karatarakis, `ExpSeries.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
-/

public section

namespace Polynomial

variable {K : Type*} [SeminormedCommRing K] [IsUltrametricDist K]

/-- In an ultrametric seminormed commutative ring, if `‖P.coeff i‖ * r ^ i ≤ B` for `r > 0`, then
each step of `expDerivFactor c m` multiplies the `r`-weighted coefficient bound by at most
`max r⁻¹ ‖c‖`. -/
theorem norm_coeff_expDerivFactor_mul_pow_le (c : K) {P : K[X]} {r B : ℝ} (hr : 0 < r)
    (hP : ∀ i, ‖P.coeff i‖ * r ^ i ≤ B) (m i : ℕ) :
    ‖(expDerivFactor c m P).coeff i‖ * r ^ i ≤ max r⁻¹ ‖c‖ ^ m * B := by
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hP 0)
  have : 0 ≤ max r⁻¹ ‖c‖ := le_max_of_le_right (norm_nonneg c)
  induction m generalizing i with
  | zero => simpa using hP i
  | succ m ih =>
    set Q := expDerivFactor c m P
    have hderiv : ‖Q.coeff (i + 1) * ((i : K) + 1)‖ ≤ ‖Q.coeff (i + 1)‖ := by
      have hnsmul : Q.coeff (i + 1) * ((i : K) + 1) = (i + 1) • Q.coeff (i + 1) := by
        rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
      rw [hnsmul]
      exact IsUltrametricDist.norm_nsmul_le _ _
    rw [expDerivFactor_succ_apply, coeff_add, coeff_derivative, coeff_C_mul]
    refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
      (by positivity)).trans ?_
    rw [max_mul_of_nonneg _ _ (by positivity), pow_succ', mul_assoc]
    refine max_le ?_ ?_
    · calc
        ‖Q.coeff (i + 1) * ((i : K) + 1)‖ * r ^ i
            ≤ ‖Q.coeff (i + 1)‖ * r ^ i := by gcongr
        _ = ‖Q.coeff (i + 1)‖ * r ^ i * (r⁻¹ * r) := by rw [inv_mul_cancel₀ hr.ne', mul_one]
        _ = r⁻¹ * (‖Q.coeff (i + 1)‖ * r ^ (i + 1)) := by
            rw [pow_succ]
            ring
        _ ≤ r⁻¹ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_left (ih (i + 1)) (by positivity)
        _ ≤ max r⁻¹ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc
        ‖c * Q.coeff i‖ * r ^ i
            ≤ ‖c‖ * (‖Q.coeff i‖ * r ^ i) := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
        _ ≤ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_left (ih i) (norm_nonneg c)
        _ ≤ max r⁻¹ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- In an ultrametric seminormed commutative ring, applying `expDerivFactor c m` multiplies a
uniform bound on the coefficients of `P` by at most `max 1 ‖c‖ ^ m`. -/
theorem norm_coeff_expDerivFactor_le (c : K) {P : K[X]} {B : ℝ}
    (hP : ∀ i, ‖P.coeff i‖ ≤ B) (m i : ℕ) :
    ‖(expDerivFactor c m P).coeff i‖ ≤ max 1 ‖c‖ ^ m * B := by
  simpa using norm_coeff_expDerivFactor_mul_pow_le c one_pos (by simpa using hP) m i

/-- Ultrametric evaluation bound for `expDerivFactor c m P` on the closed ball `‖x‖ ≤ r` (`r > 0`)
from an `r`-weighted coefficient bound on `P`. -/
theorem norm_eval_expDerivFactor_le_of_mul_pow_le (c : K) {P : K[X]} {r B : ℝ} (hr : 0 < r)
    (hP : ∀ i, ‖P.coeff i‖ * r ^ i ≤ B) (m : ℕ) {x : K} (hx : ‖x‖ ≤ r) :
    ‖(expDerivFactor c m P).eval x‖ ≤ max r⁻¹ ‖c‖ ^ m * B := by
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hP 0)
  have : 0 ≤ max r⁻¹ ‖c‖ := le_max_of_le_right (norm_nonneg c)
  rw [eval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ ↦ ?_
  calc
    ‖(expDerivFactor c m P).coeff i * x ^ i‖
        ≤ ‖(expDerivFactor c m P).coeff i‖ * ‖x‖ ^ i := TauCeti.norm_mul_pow_le _ _ _
    _ ≤ ‖(expDerivFactor c m P).coeff i‖ * r ^ i := by gcongr
    _ ≤ max r⁻¹ ‖c‖ ^ m * B := norm_coeff_expDerivFactor_mul_pow_le c hr hP m i

/-- Ultrametric evaluation bound for `expDerivFactor c m P` on the closed unit ball `‖x‖ ≤ 1`. -/
theorem norm_eval_expDerivFactor_le (c : K) {P : K[X]} {B : ℝ}
    (hP : ∀ i, ‖P.coeff i‖ ≤ B) (m : ℕ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖(expDerivFactor c m P).eval x‖ ≤ max 1 ‖c‖ ^ m * B := by
  simpa using norm_eval_expDerivFactor_le_of_mul_pow_le c one_pos (by simpa using hP) m hx

end Polynomial
