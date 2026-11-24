/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Borel
public import TauCeti.RingTheory.PowerSeries.DFinite.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Formal Borel transform and D-finite power series

Over a field `K` of characteristic zero that is an algebra over a field `k`, the factorial-divided
formal Borel series `TauCeti.ePowerSeries a = ∑ (aₙ / n!) Xⁿ` is D-finite over `k` if and only if
the ordinary generating series `PowerSeries.mk a = ∑ aₙ Xⁿ` is D-finite over `k`
(`TauCeti.isDFinite_ePowerSeries_iff`).

In transcendence theory, this formal Borel equivalence is the algebraic core of the bijection
between Siegel's G-functions `∑ aₙ zⁿ` and Siegel's E-functions `∑ aₙ zⁿ / n!`: both classes share
the same geometric house and denominator bounds on `aₙ`, and differ only in whether
`PowerSeries.mk a` or `ePowerSeries a` satisfies a linear differential equation over
`(algebraicClosure ℚ ℂ)[X]`. Passing to `PowerSeries.mk a` also transfers P-recursive coefficient
properties (such as containment of all algebraic coefficients in a single number field) directly to
E-functions.

## Main results

* `TauCeti.isDFinite_ePowerSeries_iff`: the formal Borel transform `ePowerSeries a` is D-finite
  over `k` if and only if `PowerSeries.mk a` is D-finite over `k`.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1–3.2,
  §4.1.
* S. Fischler and T. Rivoal, *On Siegel's problem for E-functions*, Math. Z. **301** (2022),
  1429–1453 (arXiv:1910.06817), §1, Definition 1.
* R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press, 1999, §6.4.
-/

public section

open Polynomial
open scoped PowerSeries

namespace TauCeti

section BorelDFinite

private theorem isDFinite_mk_of_ePowerSeries {k K : Type*} [Field k] [Field K] [CharZero K]
    [Algebra k K] {a : ℕ → K} (he : PowerSeries.IsDFinite k (ePowerSeries a)) :
    PowerSeries.IsDFinite k (PowerSeries.mk a) := by
  obtain ⟨r, q, hq, h⟩ := PowerSeries.isDFinite_iff_pRecursive.mp he
  refine PowerSeries.isDFinite_iff_pRecursive.mpr
    ⟨r, fun i ↦ q i * Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i)),
      by simpa [ascPochhammer_zero, Polynomial.taylor_one] using hq, fun n ↦ ?_⟩
  have hn := congrArg (((n + r).factorial : K) * ·) (h n)
  rw [mul_zero, Finset.mul_sum] at hn
  rw [← hn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  have hadd : n + (i : ℕ) + (r - (i : ℕ)) = n + r := by omega
  have hfac : ((n + r).factorial : K) =
      ((n + i).factorial : K) *
        algebraMap k K
          ((Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i))).eval (n : k)) := by
    have hpoch := congrArg (algebraMap k K) (factorial_mul_ascPochhammer k (n + i) (r - i))
    rw [map_mul, map_natCast, map_natCast, hadd] at hpoch
    have harg : (n : k) + ((i + 1 : ℕ) : k) = ((n + i : ℕ) : k) + 1 := by push_cast; ring
    rw [← hpoch, Polynomial.taylor_eval, harg]
  have hni : ((n + i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Polynomial.eval_mul, PowerSeries.coeff_mk, coeff_ePowerSeries, Algebra.smul_def,
    Algebra.smul_def, map_mul, hfac]
  calc algebraMap k K ((q i).eval (n : k)) *
          algebraMap k K
            ((Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i))).eval (n : k)) *
          a (n + i)
      = algebraMap k K
          ((Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i))).eval (n : k)) *
          algebraMap k K ((q i).eval (n : k)) *
          (((n + i).factorial : K) * (a (n + i) / ((n + i).factorial : K))) := by
        rw [mul_div_cancel₀ _ hni]; ring
    _ = ((n + i).factorial : K) *
          algebraMap k K
            ((Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i))).eval (n : k)) *
          (algebraMap k K ((q i).eval (n : k)) * (a (n + i) / ((n + i).factorial : K))) := by
        ring

private theorem isDFinite_ePowerSeries_of_mk {k K : Type*} [Field k] [Field K] [CharZero K]
    [Algebra k K] {a : ℕ → K} (hg : PowerSeries.IsDFinite k (PowerSeries.mk a)) :
    PowerSeries.IsDFinite k (ePowerSeries a) := by
  obtain ⟨r, q, hq, h⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hg
  refine PowerSeries.isDFinite_iff_pRecursive.mpr
    ⟨r, fun i ↦ q i * Polynomial.taylor 1 (ascPochhammer k i),
      mul_ne_zero hq ((Polynomial.taylor_eq_zero 1 _).not.mpr
        (monic_ascPochhammer (S := k) r).ne_zero),
      fun n ↦ ?_⟩
  have hn0 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  refine mul_left_cancel₀ hn0 ?_
  rw [mul_zero, Finset.mul_sum, ← h n]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfac : ((n + i).factorial : K) =
      (n.factorial : K) *
        algebraMap k K ((Polynomial.taylor 1 (ascPochhammer k i)).eval (n : k)) := by
    have hpoch := congrArg (algebraMap k K) (factorial_mul_ascPochhammer k n i)
    rw [map_mul, map_natCast, map_natCast] at hpoch
    rw [← hpoch, Polynomial.taylor_eval]
  have hni : ((n + i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Polynomial.eval_mul, coeff_ePowerSeries, PowerSeries.coeff_mk, Algebra.smul_def,
    Algebra.smul_def, map_mul]
  calc (n.factorial : K) *
          (algebraMap k K ((q i).eval (n : k)) *
            algebraMap k K ((Polynomial.taylor 1 (ascPochhammer k i)).eval (n : k)) *
            (a (n + i) / ((n + i).factorial : K)))
      = algebraMap k K ((q i).eval (n : k)) *
          (((n.factorial : K) *
            algebraMap k K ((Polynomial.taylor 1 (ascPochhammer k i)).eval (n : k))) *
            (a (n + i) / ((n + i).factorial : K))) := by ring
    _ = algebraMap k K ((q i).eval (n : k)) * a (n + i) := by
        rw [← hfac, mul_div_cancel₀ _ hni]

/-- **Formal Borel transform preserves and reflects D-finiteness.** Over a field `K` of
characteristic zero that is an algebra over a field `k`, the factorial-divided series
`ePowerSeries a = ∑ (aₙ / n!) Xⁿ` is D-finite over `k` if and only if the ordinary generating
series `PowerSeries.mk a = ∑ aₙ Xⁿ` is D-finite over `k`. -/
theorem isDFinite_ePowerSeries_iff {k K : Type*} [Field k] [Field K] [CharZero K] [Algebra k K]
    (a : ℕ → K) :
    PowerSeries.IsDFinite k (ePowerSeries a) ↔ PowerSeries.IsDFinite k (PowerSeries.mk a) :=
  ⟨isDFinite_mk_of_ePowerSeries, isDFinite_ePowerSeries_of_mk⟩

end BorelDFinite

end TauCeti
