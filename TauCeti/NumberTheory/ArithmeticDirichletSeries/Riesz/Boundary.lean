/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.NumberTheory.LSeries.Newman.Tauberian
import TauCeti.NumberTheory.LSeries.SummatoryMellin

/-!
# Boundary values of first Riesz sums

Newman's Tauberian theorem gives convergence of a normalized first Riesz sum when the
summatory function has linear growth and the Dirichlet series continues holomorphically across
`Re s = 1`. The use of the bounded function `u ↦ exp(-u) * A(exp u)` follows Newman's prime
number theorem argument (D. J. Newman, *Simple analytic proof of the prime number theorem*, 1980).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- A coefficient with index `n` contributes one normalized ramp starting at `log n`. -/
private theorem integral_exp_neg_mul_rieszTerm (a : ℂ) {n : ℕ} {T : ℝ} (hn : 1 ≤ n)
    (hnT : (n : ℝ) ≤ Real.exp T) :
    (∫ u in (0 : ℝ)..T, (Ici (Real.log n)).indicator (fun t ↦ (Real.exp (-t) : ℂ) * a) u) =
      a * ((Real.exp T : ℂ) / n - 1) / (Real.exp T : ℂ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp hn0).mpr hnT
  rw [intervalIntegral.integral_of_le (hlog0.trans hlogT), integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have he : Ici (Real.log n) ∩ Ioc (0 : ℝ) T =ᵐ[volume] Ioc (Real.log n) T := by
    filter_upwards [volume.ae_ne (Real.log n)] with u hu
    simp only [mem_inter_iff, mem_Ici, mem_Ioc]
    grind
  have hexp : (∫ u in Real.log n..T, Real.exp (-u)) = (n : ℝ)⁻¹ - (Real.exp T)⁻¹ := by
    rw [intervalIntegral.integral_comp_neg, integral_exp]
    simp [Real.exp_neg, Real.exp_log hn0]
  rw [setIntegral_congr_set he, ← intervalIntegral.integral_of_le hlogT,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hexp]
  push_cast
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
  field_simp

/-- Integrating the exponentially weighted partial sums in the log variable accumulates
one ramp per coefficient, starting at `log n`. -/
private theorem integral_exp_neg_mul_summatory (a : ℕ → ℂ) (T : ℝ) :
    (∫ u in (0 : ℝ)..T, Complex.exp (-(u : ℂ)) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, a n) =
      rieszSum a (Real.exp T) / (Real.exp T : ℂ) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [rieszSum_eq_zero_of_le_one a (Real.exp_le_one_iff.mpr hT.le), zero_div,
      intervalIntegral.integral_of_ge hT.le, integral_Ioc_eq_integral_Ioo, neg_eq_zero]
    refine setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun u hu ↦ ?_)
    have hf : ⌊Real.exp u⌋₊ < 1 := (Nat.floor_lt (Real.exp_pos u).le).mpr
      (by simpa using Real.exp_lt_one_iff.mpr hu.2)
    simp [Finset.Icc_eq_empty_of_lt hf]
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  let b (n : ℕ) (u : ℝ) := (Ici (Real.log n)).indicator
    (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * a n) u
  have hind (n : ℕ) : IntervalIntegrable (b n) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hc : Continuous (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * a n) := by fun_prop
    exact (hc.intervalIntegrable 0 T).1.indicator measurableSet_Ici
  calc
    _ = ∫ u in (0 : ℝ)..T, ∑ n ∈ S, b n u := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      rw [uIcc_of_le hT] at hu
      rw [Finset.mul_sum, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
      suffices hb : ∀ n : ℕ, 1 ≤ n →
          b n u = if n ≤ ⌊Real.exp u⌋₊ then (Real.exp (-u) : ℂ) * a n else 0 by
        refine (Finset.sum_congr rfl (fun n hn ↦ ?_)).trans (Finset.sum_subset
          (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.exp_le_exp.mpr hu.2))) ?_)
        · simp [hb n (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2]
        · intro n hn hn'
          have h := (Finset.mem_Icc.mp hn).1
          exact (hb n h).trans (ite_eq_right fun hle ↦ hn' (Finset.mem_Icc.mpr ⟨h, hle⟩))
      intro n hn
      have hn0 := Nat.ne_zero_of_lt hn
      simp [b, indicator_apply, Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn), Nat.le_floor_iff' hn0]
    _ = ∑ n ∈ S, ∫ u in (0 : ℝ)..T, b n u := intervalIntegral.integral_finsetSum fun n _ ↦ hind n
    _ = _ := by
      rw [rieszSum_def, Finset.sum_div]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      obtain ⟨hn₁, hnf⟩ := Finset.mem_Icc.mp hn
      exact integral_exp_neg_mul_rieszTerm (a n) hn₁
        ((Nat.le_floor_iff' (Nat.ne_zero_of_lt hn₁)).mp hnf)

/-- If the partial sums of `a` have linear growth and its Dirichlet series has a holomorphic
continuation to the line `Re s = 1`, the first Riesz sum divided by its cutoff tends to the
value of the continuation at `1`. No absolute convergence at `1` is required. -/
theorem tendsto_rieszSum_div_of_analyticAt {a : ℕ → ℂ} {F : ℂ → ℂ} {C : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ C * x)
    (hF : ∀ s : ℂ, s.re = 1 → AnalyticAt ℂ F s)
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum a s (F s)) :
    Tendsto (fun x : ℝ ↦ rieszSum a x / (x : ℂ)) atTop (𝓝 (F 1)) := by
  let A : ℝ → ℂ := fun x ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n
  let g : ℝ → ℂ := fun u ↦ Complex.exp (-(u : ℂ)) * A (Real.exp u)
  let G : ℂ → ℂ := fun z ↦ F (z + 1) / (z + 1)
  have hA : Measurable A := (measurable_of_countable (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Icc 1 N, a n)).comp Nat.measurable_floor
  have hg : Measurable g := by fun_prop
  have hG (z : ℂ) (hz : z.re = 0) : AnalyticAt ℂ G z := by
    have hre : (z + 1).re = 1 := by simp [hz]
    have hne : z + 1 ≠ 0 := by intro h; simp [h] at hre
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w + 1) z := analyticAt_id.add analyticAt_const
    exact ((hF _ hre).comp (f := fun w : ℂ ↦ w + 1) hshift).div hshift hne
  have hLap (z : ℂ) (hz : 0 < z.re) : G z =
      ∫ u in Set.Ici (0 : ℝ), g u * Complex.exp (-z * u) := by
    have h := hseries (z + 1) (by simpa using hz)
    have hl := h.LSeriesSummable.hasLaplace_summatory_comp_exp (by simp; linarith)
    have hshift := (hasLaplace_cexp_mul_smul_iff (s := z) (w := -1)).mpr
      (by simpa using hl)
    rw [integral_Ici_eq_integral_Ioi]
    calc
      _ = ∫ u in Ioi (0 : ℝ), Complex.exp (-z * u) * g u := by
        simpa only [G, g, A, h.LSeries_eq, smul_eq_mul, neg_one_mul, mul_neg_one] using
          hshift.integral_eq.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun _ ↦ mul_comm _ _)
  have hlim := LSeries.newmanLaplace_tendsto_integral_of_analyticAt hg.aestronglyMeasurable
    (M := C) (fun u hu ↦ by
      rw [Set.mem_Ici] at hu
      dsimp only [g]
      rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
      calc _ ≤ Real.exp (-u) * (C * Real.exp u) :=
              mul_le_mul_of_nonneg_left (hbound _ (Real.one_le_exp hu)) (Real.exp_pos _).le
        _ = C := by rw [mul_left_comm, ← Real.exp_add]; simp)
    hG hLap
  have hlog := hlim.comp Real.tendsto_log_atTop
  simp only [G, zero_add, div_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have he := integral_exp_neg_mul_summatory a (Real.log x)
  rwa [Real.exp_log (zero_lt_one.trans_le hx)] at he

end TauCeti
