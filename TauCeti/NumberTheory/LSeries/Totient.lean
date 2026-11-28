/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.Twist

/-!
# The Dirichlet series of Euler's totient

The series of the canonical `Nat.totient` coefficients converges absolutely exactly on
`Re s > 2`, where its sum is `ζ(s - 1) / ζ(s)`. The divisor identity `∑ d ∣ n, φ(d) = n`
turns its convolution with the constant-one sequence into the identity sequence.

The quotient argument is adapted from `LSeries_totient_eq` in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT].
The exact convergence boundary follows from the same convolution identity and translation
of Dirichlet series, rather than an additional estimate on primes.

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/f2692ef9a88ca93932d61265c73dd3491fbc08d8/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1914-L1982
-/

public section

open Nat Complex ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace TauCeti

private theorem totient_convolution_one :
    _root_.LSeries.convolution (fun n ↦ (n.totient : ℂ)) 1 = fun n : ℕ ↦ (n : ℂ) := by
  let f : ArithmeticFunction ℂ := ⟨fun n ↦ (n.totient : ℂ), by simp⟩
  have hf (n : ℕ) : f n = (n.totient : ℂ) := rfl
  have hφ : toArithmeticFunction (fun n ↦ (n.totient : ℂ)) = f :=
    toArithmeticFunction_eq_self f
  have hz : toArithmeticFunction (1 : ℕ → ℂ) = (ζ : ArithmeticFunction ℂ) :=
    (toArithmeticFunction_congr (const_one_eq_zeta (R := ℂ))).trans
      (toArithmeticFunction_eq_self (ζ : ArithmeticFunction ℂ))
  funext n
  rw [_root_.LSeries.convolution, hφ, hz, coe_mul_zeta_apply]
  simp only [hf]
  rw [← Nat.cast_sum, Nat.sum_totient]

/-- The totient Dirichlet series converges absolutely exactly on `Re s > 2`. -/
theorem LSeriesSummable_totient_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (n.totient : ℂ)) s ↔ 2 < s.re := by
  constructor
  · intro hf
    by_contra! hs
    have hf2 : LSeriesSummable (fun n ↦ (n.totient : ℂ)) 2 :=
      hf.of_re_le_re (by simpa using hs)
    have hc := hf2.convolution (LSeriesSummable_one_iff.mpr (by norm_num : 1 < (2 : ℂ).re))
    rw [totient_convolution_one] at hc
    have hid : LSeriesSummable (fun n ↦ (1 : ℂ) * (n : ℂ) ^ (1 : ℂ)) 2 := by
      simpa using hc
    have hone := (LSeries.LSeriesSummable_mul_natCast_cpow_iff 1 1 2).mp hid
    rw [LSeriesSummable_one_iff] at hone
    norm_num at hone
  · intro hs
    apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hs
    refine ⟨1, fun n _ ↦ ?_⟩
    have hexponent : (2 : ℝ) - 1 = 1 := by norm_num
    simpa only [Complex.norm_natCast, hexponent, Real.rpow_one, one_mul] using
      (Nat.cast_le (α := ℝ)).mpr (Nat.totient_le n)

/-- The abscissa of absolute convergence of the totient Dirichlet series is two. -/
theorem abscissaOfAbsConv_totient :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (n.totient : ℂ)) = 2 :=
  mod_cast LSeries.abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_totient_iff

/-- The totient Dirichlet series has sum `ζ(s - 1) / ζ(s)` on `Re s > 2`. -/
theorem LSeriesHasSum_totient {s : ℂ} (hs : 2 < s.re) :
    LSeriesHasSum (fun n ↦ (n.totient : ℂ)) s
      (riemannZeta (s - 1) / riemannZeta s) := by
  have hs1 : 1 < s.re := by linarith
  have hs_sub : 1 < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hf := LSeriesSummable_totient_iff.mpr hs
  have hc := hf.LSeriesHasSum.convolution (LSeriesHasSum_one hs1)
  rw [totient_convolution_one] at hc
  have hid : LSeriesHasSum (fun n ↦ (1 : ℂ) * (n : ℂ) ^ (1 : ℂ)) s
      (riemannZeta (s - 1)) :=
    (LSeries.LSeriesHasSum_mul_natCast_cpow_iff 1 1 s _).mpr (LSeriesHasSum_one hs_sub)
  have hid_value : _root_.LSeries (fun n : ℕ ↦ (n : ℂ)) s = riemannZeta (s - 1) := by
    simpa using hid.LSeries_eq
  have heq := hc.LSeries_eq.symm.trans hid_value
  refine LSeriesHasSum_iff.mpr ⟨hf, ?_⟩
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs1)).mpr heq

/-- The totient Dirichlet series is `ζ(s - 1) / ζ(s)` on `Re s > 2`. -/
theorem LSeries_totient {s : ℂ} (hs : 2 < s.re) :
    _root_.LSeries (fun n ↦ (n.totient : ℂ)) s = riemannZeta (s - 1) / riemannZeta s :=
  (LSeriesHasSum_totient hs).LSeries_eq

end TauCeti
