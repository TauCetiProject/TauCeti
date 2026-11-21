/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Finset.Floor
import Mathlib.Order.SuccPred.Int
import Mathlib.Tactic.Linarith

/-!
# Exponential sums over integer points of real intervals

The phase is evaluated at the integers in a closed interval, using `Real.fourierChar`
for the convention `e(x) = exp(2πix)`. Real half-open intervals have an equivalent sum
with a shifted left endpoint. The forward-difference identity expresses the lag sums
in van der Corput differencing as interval exponential sums again.

## References

* J. Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*,
  arXiv:2407.02094, Lemma 6 and Theorem 7 (half-open intervals and forward differences).
-/

public section

open Finset
open scoped ComplexConjugate

namespace TauCeti

/-- The sum of `exp(2πi f(n))` over the integers `n` in the closed real interval `[a, b]`. -/
noncomputable def intervalExpSum (f : ℝ → ℝ) (a b : ℝ) : ℂ :=
  ∑ n ∈ Icc ⌈a⌉ ⌊b⌋, (Real.fourierChar (f n) : ℂ)

/-- Express the interval exponential sum as a finite sum with integer endpoints. -/
theorem intervalExpSum_def (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum f a b = ∑ n ∈ Icc ⌈a⌉ ⌊b⌋, (Real.fourierChar (f n) : ℂ) := (rfl)

/-- Only the values of the phase at the integers in the interval matter. -/
theorem intervalExpSum_congr {f g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ n : ℤ, (n : ℝ) ∈ Set.Icc a b → f n = g n) :
    intervalExpSum f a b = intervalExpSum g a b := by
  rw [intervalExpSum_def, intervalExpSum_def]
  exact sum_congr rfl fun n hn ↦ congrArg (fun x ↦ (Real.fourierChar x : ℂ))
    (h n (Int.cast_mem_Icc_iff.mpr hn))

/-- An interval with no integer points has exponential sum zero. -/
theorem intervalExpSum_eq_zero_of_floor_lt_ceil (f : ℝ → ℝ) {a b : ℝ}
    (h : ⌊b⌋ < ⌈a⌉) : intervalExpSum f a b = 0 := by
  rw [intervalExpSum_def, Icc_eq_empty_of_lt h, sum_empty]

/-- Reversed endpoints give the empty sum. -/
theorem intervalExpSum_eq_zero_of_lt (f : ℝ → ℝ) {a b : ℝ} (h : b < a) :
    intervalExpSum f a b = 0 :=
  intervalExpSum_eq_zero_of_floor_lt_ceil f (Int.floor_lt_ceil_of_lt h)

/-- At a single integer endpoint the exponential sum is the corresponding phase factor. -/
@[simp] theorem intervalExpSum_intCast_self (f : ℝ → ℝ) (n : ℤ) :
    intervalExpSum f n n = (Real.fourierChar (f n) : ℂ) := by
  simp [intervalExpSum_def]

/-- A constant phase contributes the same phase factor for each integer point. -/
@[simp] theorem intervalExpSum_const (c a b : ℝ) :
    intervalExpSum (fun _ ↦ c) a b =
      ((⌊b⌋ + 1 - ⌈a⌉).toNat : ℂ) * (Real.fourierChar c : ℂ) := by
  simp [intervalExpSum_def, Int.card_Icc, nsmul_eq_mul]

/-- Adding a constant to the phase multiplies the sum by its unit phase factor. -/
theorem intervalExpSum_add_const (f : ℝ → ℝ) (c a b : ℝ) :
    intervalExpSum (fun x ↦ f x + c) a b = intervalExpSum f a b * (Real.fourierChar c : ℂ) := by
  simp [intervalExpSum_def, AddChar.map_add_eq_mul, sum_mul]

/-- Adding a linear phase of integer slope leaves the exponential sum unchanged. -/
@[simp] theorem intervalExpSum_add_intCast_mul (f : ℝ → ℝ) (k : ℤ) (a b : ℝ) :
    intervalExpSum (fun x ↦ f x + (k : ℝ) * x) a b = intervalExpSum f a b := by
  rw [intervalExpSum_def, intervalExpSum_def]
  refine sum_congr rfl fun n _ ↦ ?_
  have h : (Real.fourierChar ((k : ℝ) * (n : ℝ)) : ℂ) = 1 := by
    rw [← Int.cast_mul, Real.fourierChar_apply]
    simpa only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat,
      mul_left_comm, mul_assoc]
      using Complex.exp_int_mul_two_pi_mul_I (k * n)
  simp [AddChar.map_add_eq_mul, h]

/-- Negating the phase conjugates the exponential sum. -/
@[simp] theorem intervalExpSum_neg (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum (fun x ↦ -f x) a b = conj (intervalExpSum f a b) := by
  simp only [intervalExpSum_def, map_sum, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- Splitting after the integer `c` leaves the next integer `c + 1` in the right sum. -/
theorem intervalExpSum_eq_add (f : ℝ → ℝ) {a b : ℝ} {c : ℤ}
    (ha : a ≤ (c : ℝ) + 1) (hb : (c : ℝ) ≤ b) :
    intervalExpSum f a b = intervalExpSum f a c + intervalExpSum f ((c : ℝ) + 1) b := by
  have hc : ⌈a⌉ - 1 ≤ c := by
    have : ⌈a⌉ ≤ c + 1 := Int.ceil_le.mpr (by exact_mod_cast ha)
    omega
  have hcb : c ≤ ⌊b⌋ := Int.le_floor.mpr hb
  have hs := sum_union (f := fun n : ℤ ↦ (Real.fourierChar (f n) : ℂ))
    (Ioc_disjoint_Ioc_of_le (a := ⌈a⌉ - 1) (d := ⌊b⌋) (le_refl c))
  rw [Ioc_union_Ioc_eq_Ioc hc hcb] at hs
  simpa only [intervalExpSum_def, Int.floor_intCast, Int.ceil_add_one, Int.ceil_intCast,
    Icc_add_one_left_eq_Ioc c ⌊b⌋, Ioc_sub_one_left_eq_Icc] using hs

/-- The norm is at most the number of integer points, truncated at zero for an empty interval. -/
theorem norm_intervalExpSum_le (f : ℝ → ℝ) (a b : ℝ) :
    ‖intervalExpSum f a b‖ ≤ max 0 ((⌊b⌋ : ℝ) - (⌈a⌉ : ℝ) + 1) := by
  calc
    ‖intervalExpSum f a b‖ ≤ ((Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by
      simpa [intervalExpSum_def] using
        (norm_sum_le (Icc ⌈a⌉ ⌊b⌋) fun n ↦ (Real.fourierChar (f n) : ℂ))
    _ = _ := by
      rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_eq_max, Int.cast_max, max_comm]
      push_cast
      congr 1
      linarith

/-- The norm is at most the interval length plus one, whenever this bound is nonnegative. -/
theorem norm_intervalExpSum_le_sub_add_one (f : ℝ → ℝ) {a b : ℝ} (h : a ≤ b + 1) :
    ‖intervalExpSum f a b‖ ≤ b - a + 1 := by
  apply (norm_intervalExpSum_le f a b).trans (max_le _ _)
  · linarith
  · linarith [Int.floor_le b, Int.le_ceil a]

/-- The sum over `a < n ≤ b` is the closed sum starting at the first integer strictly above `a`. -/
theorem intervalExpSum_eq_sum_Ioc (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum f ((⌊a⌋ : ℝ) + 1) b =
      ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, (Real.fourierChar (f n) : ℂ) := by
  simp only [intervalExpSum_def, Int.ceil_add_one, Int.ceil_intCast, Icc_add_one_left_eq_Ioc]

/-- The lag correlation for the phase `f`, truncated on the right by the shift `h`, is the
exponential sum of the forward difference `f(x + h) - f(x)`. For `h ≥ 0`, the truncation keeps
both `n` and `n + h` in the original half-open interval `(a, b]`. -/
theorem sum_Ioc_mul_conj_fourierChar_eq_intervalExpSum (f : ℝ → ℝ) (a b h : ℝ) :
    (∑ n ∈ Ioc ⌊a⌋ ⌊b - h⌋,
      (Real.fourierChar (f ((n : ℝ) + h)) : ℂ) * conj (Real.fourierChar (f n) : ℂ)) =
      intervalExpSum (fun x ↦ f (x + h) - f x) ((⌊a⌋ : ℝ) + 1) (b - h) := by
  rw [intervalExpSum_eq_sum_Ioc]
  apply sum_congr rfl
  intro n _
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

end TauCeti
