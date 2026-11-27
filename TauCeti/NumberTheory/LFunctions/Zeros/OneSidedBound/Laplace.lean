/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Laplace
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Laplace transform of the signed prime remainder

Character orthogonality identifies the Dirichlet series of the signed von Mangoldt weight
on the class of `1`. After first Riesz smoothing, the logarithmic change of variables gives
an absolutely convergent Laplace integral. Its expression in terms of the mean of logarithmic
L-function derivatives is suitable for continuation and analysis of its poles.

The normalization follows `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean` and
`New.integral_primeRemainder` in `grh/src/New/Reduction/Zeros/PrimeError.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open ArithmeticFunction Complex DirichletCharacter Filter
open scoped Topology

namespace TauCeti.OneSidedBound

variable {d q : ℕ} [Fact d.Prime] [NeZero q]

-- Identify the twist used in the prime remainder with the Legendre twist at level `q * d`.
private theorem quadraticTwist_eq_legendreTwist (χ : DirichletCharacter ℂ q) :
    quadraticTwist d χ = χ.legendreTwist d := by
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  refine MulChar.ext fun a ↦ ?_
  rw [quadraticTwist_apply, ← ZMod.natCast_zmod_val (a : ZMod (q * d)),
    legendreTwist_apply_natCast]
  simp [legendreSym]

open Classical in
/-- The polar counterterm counts the untwisted principal character with sign `+1` and each
principal twist with sign `-1`. -/
private theorem LSeriesHasSum_primeWeight_sub_principalTwists {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s
      ((1 - ∑ χ : DirichletCharacter ℂ q, if quadraticTwist d χ = 1 then (1 : ℂ) else 0) /
        ((q.totient : ℂ) * (s - 1)) + (q.totient : ℂ)⁻¹ + logDerivMean d q s) := by
  classical
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have h (χ : DirichletCharacter ℂ q) :=
    (χ.LSeriesHasSum_twist_vonMangoldt hs).sub
      ((quadraticTwist d χ).LSeriesHasSum_twist_vonMangoldt hs)
  have hsum := (LSeriesHasSum.sum (S := Finset.univ) fun χ _ ↦ h χ).smul (q.totient : ℂ)⁻¹
  have hcoeff : LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s _ :=
    (LSeriesHasSum_congr s _ ?_).mp hsum
  · convert hcoeff using 1
    simp only [logDerivMean_def]
    have hsplit (a b c e : ℂ) : a - b - (c - e) = (a - c) + (e - b) := by abel
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro n _
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.sub_apply,
      quadraticTwist_eq_legendreTwist, legendreTwist_apply_natCast, ← sub_mul]
    simp_rw [← mul_one_sub, mul_right_comm (_ : ℂ) (1 - _), ← Finset.sum_mul, ← mul_assoc]
    rw [sum_characters_eq]
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    by_cases hn : (n : ZMod q) = 1 <;>
      simp [primeWeight_def, hn, hφ]

/-- For an odd prime `d` coprime to `q` and `Re s > 1`, the Dirichlet series of the signed
weight `primeWeight d q` sums to `s / (φ(q) * (s - 1)) + G_q(s)`, where `φ` is Euler's
totient and `G_q = logDerivMean d q`. -/
theorem LSeriesHasSum_primeWeight (hd : d ≠ 2) (hq : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s
      (s / ((q.totient : ℂ) * (s - 1)) + logDerivMean d q s) := by
  classical
  have hne (χ : DirichletCharacter ℂ q) : quadraticTwist d χ ≠ 1 :=
    (quadraticTwist_eq_legendreTwist (d := d) χ) ▸ χ.legendreTwist_ne_one d hd hq
  convert LSeriesHasSum_primeWeight_sub_principalTwists (d := d) (q := q) hs using 1
  simp only [ite_eq_right (hne _), Finset.sum_const_zero, sub_zero]
  have hs₁ : s - 1 ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hs)
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp
  ring

/-- The logarithmic-derivative mean is analytic at every `s` with `Re s ≥ 1`. -/
theorem analyticAt_logDerivMean_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (logDerivMean d q) s := by
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have h {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
      AnalyticAt ℂ (logDeriv χ.entireLFunction) s :=
    (χ.analyticAt_entireLFunction s).logDeriv (χ.entireLFunction_ne_zero_of_one_le_re hs)
  simp_rw [funext (logDerivMean_def d q)]
  exact ((Finset.analyticAt_fun_sum _ fun χ _ ↦ (h (quadraticTwist d χ)).sub (h χ)).sub
    analyticAt_const).div_const

/-- The value of the logarithmic-derivative mean at `1` is real. -/
@[simp] theorem ofReal_re_logDerivMean_one :
    ((logDerivMean d q 1).re : ℂ) = logDerivMean d q 1 := by
  -- Approach from the right along the real line, where the series and polar counterterm are real.
  have hc := (analyticAt_logDerivMean_of_one_le_re (d := d) (q := q) (s := 1)
    (by simp)).continuousAt
  have hreal : ContinuousAt (fun x : ℝ ↦ logDerivMean d q x) 1 :=
    (by simpa only [ofReal_one] using hc : ContinuousAt (logDerivMean d q) ((1 : ℝ) : ℂ)).comp
      continuous_ofReal.continuousAt
  apply tendsto_nhds_unique (f := fun x : ℝ ↦ logDerivMean d q x) (l := 𝓝[>] 1)
    ((continuous_ofReal.continuousAt.comp (continuous_re.continuousAt.comp hreal)).tendsto.mono_left
      nhdsWithin_le_nhds |>.congr' ?_) (by simpa using hreal.continuousWithinAt.tendsto)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := by simpa using (Set.mem_Ioi.mp hx)
  have hsum := (LSeriesHasSum_primeWeight_sub_principalTwists (d := d) (q := q) hx').LSeries_eq
  have hconj := TauCeti.LSeries.LSeries_star (fun n ↦ (primeWeight d q n : ℂ)) (x : ℂ)
  simp only [Pi.star_def, Complex.star_def, Complex.conj_ofReal] at hconj
  rw [hsum] at hconj
  exact Complex.conj_eq_iff_re.mp (by
    simpa only [map_add, map_div₀, map_mul, map_sub, map_inv₀, map_one, _root_.map_zero,
      map_natCast, map_sum, apply_ite, Complex.conj_ofReal, add_right_inj] using hconj.symm)

/-- After division by its length, the first Riesz sum of the prime weights gives the smoothed
part of `primeRemainder`. -/
theorem ofReal_primeRemainder_eq (y : ℝ) :
    (primeRemainder d q y : ℂ) =
      rieszSum (fun n ↦ (primeWeight d q n : ℂ)) y / (y : ℂ) -
        (Real.log y : ℂ) / (q.totient : ℂ) - logDerivMean d q 1 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [primeRemainder_def]
  simp only [primeRemainder_def, ofReal_sub, ofReal_sum, ofReal_mul, ofReal_div, ofReal_one,
    ofReal_natCast, ofReal_re_logDerivMean_one, rieszSum_def, Finset.sum_div]
  congr 2
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy
  rw [mul_div_assoc, sub_div, div_right_comm, div_self hy']

/-- For an odd prime `d` coprime to `q` and `Re s > 1`, the absolutely convergent Laplace
transform of `u ↦ R_q(exp u)` at `s - 1` is `(G_q(s) / s - G_q(1)) / (s - 1)`. -/
theorem hasLaplace_primeRemainder (hd : d ≠ 2) (hq : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ (primeRemainder d q (Real.exp u) : ℂ)) (s - 1)
      ((logDerivMean d q s / s - logDerivMean d q 1) / (s - 1)) := by
  have hsum := LSeriesHasSum_primeWeight hd hq hs
  have h := hasLaplace_normalized_riesz_remainder hs hsum.LSeriesSummable
    (q.totient : ℂ)⁻¹ (logDerivMean d q 1)
  convert h using 1
  · ext u
    rw [ofReal_primeRemainder_eq, Real.log_exp]
    simp [div_eq_mul_inv, mul_comm]
  · rw [hsum.LSeries_eq]
    have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    rw [add_div, div_right_comm, div_self hs₀, ← div_div, one_div, add_sub_cancel_left]

end TauCeti.OneSidedBound
