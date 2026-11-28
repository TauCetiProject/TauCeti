/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Laplace
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Laplace transform of the one-sided prime remainder

The signed prime weight is expanded by character orthogonality. Its Dirichlet series is the
sum of the principal polar term and the mean of logarithmic derivatives `G_q`. After passing to
the logarithmic variable, the Laplace transform of the normalized remainder is the divided
difference at `1` of `s ↦ G_q(s) / s`. This expression lets one use zero-free regions for the
individual characters to study the decay of the remainder.

The normalization is that of `New.integral_primeRemainder` in `New/Reduction/Zeros/PrimeError`
of lsernau/grh-lean (commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open ArithmeticFunction Complex DirichletCharacter Filter
open scoped ArithmeticFunction Topology

namespace TauCeti.OneSidedBound

variable {d q : ℕ} [Fact d.Prime] [NeZero q]

/-- The compensated mean is analytic wherever all the pole-removed L-functions in it are
nonzero. In particular, this applies on `Re s ≥ 1`. -/
theorem analyticAt_logDerivMean {s : ℂ}
    (h : haveI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
      ∀ ψ : DirichletCharacter ℂ q,
        ψ.entireLFunction s ≠ 0 ∧ (ψ.legendreTwist d).entireLFunction s ≠ 0) :
    AnalyticAt ℂ (logDerivMean d q) s := by
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have ha := (Finset.analyticAt_fun_sum (Finset.univ : Finset (DirichletCharacter ℂ q)) fun ψ _ ↦
    (((ψ.legendreTwist d).analyticAt_entireLFunction s).logDeriv (h ψ).2).sub
      ((ψ.analyticAt_entireLFunction s).logDeriv (h ψ).1)).sub
    (analyticAt_const (v := (1 : ℂ)))
  convert ha.div (analyticAt_const (v := (q.totient : ℂ)))
    (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne') using 1
  ext z : 1
  simp [logDerivMean_def, quadraticTwist_eq_legendreTwist]

/-- The logarithmic-derivative mean is analytic at every `s` with `Re s ≥ 1`. -/
theorem analyticAt_logDerivMean_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (logDerivMean d q) s :=
  analyticAt_logDerivMean fun ψ ↦ ⟨ψ.entireLFunction_ne_zero_of_one_le_re hs,
    (ψ.legendreTwist d).entireLFunction_ne_zero_of_one_le_re hs⟩

open Classical in
/-- Count the principal members of the twisted family in the polar contribution. -/
private theorem LSeriesHasSum_primeWeight_with_principal_twists {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s
      ((s - ((Finset.univ.filter
        fun ψ : DirichletCharacter ℂ q ↦ ψ.legendreTwist d = 1).card : ℂ)) /
        ((q.totient : ℂ) * (s - 1)) + logDerivMean d q s) := by
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have hterm (ψ : DirichletCharacter ℂ q) :
      LSeriesHasSum (fun n : ℕ ↦ ψ n * Λ n - ψ.legendreTwist d n * Λ n) s
        (((if ψ = 1 then 1 else 0) - (if ψ.legendreTwist d = 1 then 1 else 0)) / (s - 1) +
          (logDeriv (ψ.legendreTwist d).entireLFunction s - logDeriv ψ.entireLFunction s)) := by
    convert (ψ.LSeriesHasSum_twist_vonMangoldt hs).sub
      ((ψ.legendreTwist d).LSeriesHasSum_twist_vonMangoldt hs) using 1
    ring
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum := (LSeriesHasSum.sum (S := Finset.univ) fun ψ _ ↦ hterm ψ).smul
    (q.totient : ℂ)⁻¹
  convert (LSeriesHasSum_congr s _ ?_).mp hsum using 1
  · have hs₁ : s ≠ 1 := ne_of_apply_ne re hs.ne'
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_boole, logDerivMean_def,
      quadraticTwist_eq_legendreTwist]
    field_simp [hq, sub_ne_zero.mpr hs₁]
    ring
  · intro n _
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, legendreTwist_apply_natCast]
    simp_rw [← sub_mul, ← mul_one_sub, mul_right_comm _ (1 - (legendreSym d n : ℂ)),
      ← Finset.sum_mul]
    have hres := vonMangoldt.residueClass_apply (a := (1 : ZMod q)) isUnit_one n
    simp only [ZMod.inv_one, map_one, one_mul, ← Finset.sum_mul] at hres
    rw [← mul_assoc, ← hres, primeWeight_def]
    by_cases hn : (n : ZMod q) = 1 <;> simp [vonMangoldt.residueClass, hn]

/-- On `Re s > 1`, the series of the signed Legendre weight is
`s / (φ(q) * (s - 1)) + G_q(s)`. If `d` is odd and coprime to `q`, the only principal
contribution comes from the untwisted family. -/
theorem LSeriesHasSum_primeWeight (hd : d ≠ 2) (hc : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s
      (s / ((q.totient : ℂ) * (s - 1)) + logDerivMean d q s) := by
  classical
  simpa [legendreTwist_ne_one _ d hd hc] using
    LSeriesHasSum_primeWeight_with_principal_twists (d := d) (q := q) hs

/-- The endpoint value of the compensated mean is real. -/
@[simp] theorem ofReal_re_logDerivMean_one :
    ((logDerivMean d q 1).re : ℂ) = logDerivMean d q 1 := by
  classical
  have ha : AnalyticAt ℂ (logDerivMean d q) 1 := analyticAt_logDerivMean_of_one_le_re (by simp)
  have ht : Tendsto (fun t : ℝ ↦ logDerivMean d q (t : ℂ)) (𝓝[>] 1)
      (𝓝 (logDerivMean d q 1)) := by
    have hr : ContinuousAt (fun t : ℝ ↦ (t : ℂ)) 1 := continuous_ofReal.continuousAt
    exact ha.continuousAt.tendsto.comp (by simpa using hr.tendsto.mono_left nhdsWithin_le_nhds)
  apply conj_eq_iff_re.mp
  refine tendsto_nhds_unique_of_eventuallyEq (continuous_conj.continuousAt.tendsto.comp ht) ht ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hs : 1 < (t : ℂ).re := by rwa [ofReal_re]
  have he := (LSeriesHasSum_primeWeight_with_principal_twists (d := d) (q := q) hs).LSeries_eq
  have hcoeff : star (fun n ↦ (primeWeight d q n : ℂ)) = fun n ↦ (primeWeight d q n : ℂ) := by
    ext n : 1
    simp
  have hconj := TauCeti.LSeries.LSeries_star (fun n ↦ (primeWeight d q n : ℂ)) (t : ℂ)
  rw [hcoeff, star_def, conj_ofReal, he] at hconj
  simp only [map_add, map_div₀, map_mul, map_sub, map_one, conj_ofReal, conj_natCast] at hconj
  exact add_left_cancel hconj.symm

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

/-- The one-sided Laplace transform of `v ↦ R_q(exp v)` at `s - 1` is the divided difference
at `1` of `s ↦ G_q(s) / s`, for `1 < Re s`. -/
theorem hasLaplace_primeRemainder (hd : d ≠ 2) (hc : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun v : ℝ ↦ (primeRemainder d q (Real.exp v) : ℂ)) (s - 1)
      ((logDerivMean d q s / s - logDerivMean d q 1) / (s - 1)) := by
  have hseries := LSeriesHasSum_primeWeight hd hc hs
  have h := hasLaplace_normalized_riesz_remainder hs hseries.LSeriesSummable
    (q.totient : ℂ)⁻¹ (logDerivMean d q 1)
  convert h using 1
  · ext v
    rw [ofReal_primeRemainder_eq, Real.log_exp]
    simp [div_eq_mul_inv, mul_comm]
  · rw [hseries.LSeries_eq]
    have hs₀ : s ≠ 0 := ne_of_apply_ne re (by simp; linarith)
    have hs₁ : s ≠ 1 := ne_of_apply_ne re hs.ne'
    field_simp [hs₀, sub_ne_zero.mpr hs₁,
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne']
    ring

end TauCeti.OneSidedBound
