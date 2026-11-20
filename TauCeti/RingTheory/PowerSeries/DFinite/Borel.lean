/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.DFinite.Basic
public import TauCeti.RingTheory.PowerSeries.ExponentialSeries.Basic

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.RingTheory.Polynomial.AscPochhammer

/-!
# Formal Borel transform for D-finite series

Over any field `k` inside a characteristic-zero field `K`, scaling a polynomial recurrence by
Taylor-shifted ascending Pochhammer polynomials identifies D-finiteness of `PowerSeries.mk a` with
D-finiteness of `ePowerSeries a`.

## Main results

* `TauCeti.isDFinite_mk_iff_isDFinite_ePowerSeries`: `PowerSeries.mk a` is D-finite iff
  `ePowerSeries a` is D-finite.

## References

* F. Beukers, *E-functions and G-functions*, Arizona Winter School, 2008, §3.1, §4.1.
-/

public section

open Finset PowerSeries

namespace TauCeti

/-- **Borel transform for D-finite series.** Over any field `k` inside a characteristic-zero field
`K`, the ordinary series `PowerSeries.mk a = ∑ₙ aₙ Xⁿ` is D-finite over `k` if and only if the
factorial-divided series `ePowerSeries a = ∑ₙ (aₙ / n!) Xⁿ` is D-finite over `k`. -/
theorem isDFinite_mk_iff_isDFinite_ePowerSeries {k K : Type*} [Field k] [Field K] [CharZero K]
    [Algebra k K] {a : ℕ → K} :
    PowerSeries.IsDFinite k (PowerSeries.mk a) ↔ PowerSeries.IsDFinite k (ePowerSeries a) := by
  constructor
  · intro hf
    obtain ⟨r, p, hp, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hf
    have hne : Polynomial.taylor (1 : k) (ascPochhammer k r) ≠ 0 :=
      (Polynomial.taylor_eq_zero _ _).not.mpr (monic_ascPochhammer k r).ne_zero
    refine PowerSeries.isDFinite_iff_pRecursive.mpr
      ⟨r, fun i ↦ p i * Polynomial.taylor (1 : k) (ascPochhammer k i), mul_ne_zero hp hne,
        fun n ↦ ?_⟩
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) ?_
    rw [mul_zero, mul_sum, ← hrec n]
    refine sum_congr rfl fun i _ ↦ ?_
    have hni : ((n + (i : ℕ)).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hprod : (n.factorial : K) * algebraMap k K
        ((Polynomial.taylor (1 : k) (ascPochhammer k i)).eval (n : k)) =
        ((n + (i : ℕ)).factorial : K) := by
      simpa only [add_zero, zero_add, Nat.cast_one, map_mul, map_natCast] using
        congrArg (algebraMap k K) (factorial_mul_eval_taylor_ascPochhammer k n 0 i)
    rw [Algebra.smul_def, Algebra.smul_def, coeff_ePowerSeries, coeff_mk, Polynomial.eval_mul,
      map_mul, ← mul_assoc, mul_left_comm (n.factorial : K), hprod, mul_assoc,
      mul_div_cancel₀ _ hni]
  · intro hf
    obtain ⟨r, q, hq, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hf
    refine PowerSeries.isDFinite_iff_pRecursive.mpr
      ⟨r, fun i ↦ q i * Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i)),
        by simpa using hq, fun n ↦ ?_⟩
    rw [← mul_zero ((n + r).factorial : K), ← hrec n, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hni : ((n + (i : ℕ)).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hprod : ((n + (i : ℕ)).factorial : K) * algebraMap k K
        ((Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i))).eval (n : k)) =
        ((n + r).factorial : K) := by
      simpa only [map_mul, map_natCast, Nat.add_assoc, Nat.add_sub_of_le hi] using
        congrArg (algebraMap k K) (factorial_mul_eval_taylor_ascPochhammer k n i (r - i))
    rw [Algebra.smul_def, Algebra.smul_def, coeff_mk, coeff_ePowerSeries, Polynomial.eval_mul,
      map_mul, ← hprod]
    conv_lhs => rw [← mul_div_cancel₀ (a (n + i)) hni]
    ring

end TauCeti
