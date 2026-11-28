/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.MeasureTheory.Integral.Bochner.BlockError

/-!
# Second-moment error of cutting Bessel kernels

The row of amplitude differences over a fixed first class and a fixed reduction has an
absolute integral budget. Squaring each row's budget and summing over the first classes and
reductions bounds the normalized second moment of the error. No count of the terms within a
block or of the second classes is needed.

The comparison is the cut-error step of `New.Filling.secondMoment_sub_cut_le` in
`grh/src/New/Spanning/RemainingTerms/Size.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- A budget of `|ν| / (2 b^n)` for the sum of the integral errors over each row of
Bessel blocks gives a normalized second-moment error at most `H / b^40`. It suffices
that the set of reductions have size at most `b^n` and that `H` dominate the number of
first classes. The kernels include the cutoff factors used in each block. The exponent
`n` can be taken to be `k^3 * f` when the rank is `k` and there are `f` infinite places. -/
theorem secondMoment_sub_cut_le {X A B J V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure X} {C : Finset A} {S : Finset B} {D : Finset J}
    {I : A → B → J → Type*} {K L : (c : A) → (s : B) → (d : J) → I c s d → X → V}
    {ν H : ℝ} {b n : ℕ} (hn : 40 ≤ n) (hS : (S.card : ℝ) ≤ (b : ℝ) ^ n)
    (hC : (C.card : ℝ) ≤ H)
    (hK : ∀ c ∈ C, ∀ s ∈ S, ∀ d ∈ D, ∀ i, AEStronglyMeasurable (K c s d i) μ)
    (hL : ∀ c ∈ C, ∀ s ∈ S, ∀ d ∈ D, ∀ i, AEStronglyMeasurable (L c s d i) μ)
    (herror : ∀ c ∈ C, ∀ s ∈ S, (∑ d ∈ D, ∑' i, ∫⁻ x, edist (K c s d i x) (L c s d i x) ∂μ) ≤
      ENNReal.ofReal (|ν| / (2 * (b : ℝ) ^ n))) :
    (∑ c ∈ C, ∑ s ∈ S, ∑ d ∈ D,
      (dist (∑' i, ∫ x, K c s d i x ∂μ) (∑' i, ∫ x, L c s d i x ∂μ) / ν) ^ 2) ≤
      H / (b : ℝ) ^ 40 := by
  let F (c : A) (s : B) (d : J) :=
    dist (∑' i, ∫ x, K c s d i x ∂μ) (∑' i, ∫ x, L c s d i x ∂μ)
  have hH : 0 ≤ H := (Nat.cast_nonneg _).trans hC
  obtain rfl | hb := Nat.eq_zero_or_pos b
  · simp [zero_pow (by omega : n ≠ 0), Nat.cast_nonpos] at hS
    simp [hS]
  by_cases hν : ν = 0
  · simpa [hν] using (by positivity : 0 ≤ H / (b : ℝ) ^ 40)
  have habs : 0 < |ν| := abs_pos.mpr hν
  have hp : 0 < (b : ℝ) ^ n := by positivity
  have hrow (c : A) (hc : c ∈ C) (s : B) (hs : s ∈ S) :
      ∑ d ∈ D, F c s d ≤ |ν| * (((b : ℝ) ^ n)⁻¹ / 2) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_sum_of_nonneg
      (fun _ _ ↦ dist_nonneg)]
    simp only [← edist_dist, div_eq_mul_inv]
    exact (Finset.sum_le_sum fun d hd ↦ edist_tsum_integral_le_tsum_lintegral_edist
      (hK c hc s hs d hd) (hL c hc s hs d hd)).trans
        (by simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using herror c hc s hs)
  have hsq (c : A) (hc : c ∈ C) (s : B) (hs : s ∈ S) :
      ∑ d ∈ D, (F c s d / ν) ^ 2 ≤ (((b : ℝ) ^ n)⁻¹ / 2) ^ 2 := by
    simp_rw [div_pow, ← sq_abs ν]
    rw [← Finset.sum_div, div_le_iff₀ (pow_pos habs 2)]
    calc
      ∑ d ∈ D, F c s d ^ 2 ≤ (∑ d ∈ D, F c s d) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ dist_nonneg
      _ ≤ (|ν| * (((b : ℝ) ^ n)⁻¹ / 2)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ dist_nonneg) (hrow c hc s hs) 2
      _ = _ := by ring
  calc
    _ ≤ ∑ _c ∈ C, ∑ _s ∈ S, (((b : ℝ) ^ n)⁻¹ / 2) ^ 2 :=
      Finset.sum_le_sum fun c hc ↦ Finset.sum_le_sum fun s hs ↦ hsq c hc s hs
    _ ≤ H * (b : ℝ) ^ n * (((b : ℝ) ^ n)⁻¹ / 2) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      gcongr
    _ = H * ((b : ℝ) ^ n)⁻¹ / 4 := by field_simp; ring
    _ ≤ H * ((b : ℝ) ^ n)⁻¹ := by linarith [mul_nonneg hH (inv_nonneg.mpr hp.le)]
    _ ≤ H / (b : ℝ) ^ 40 := by
      rw [div_eq_mul_inv]
      have hb₁ : 1 ≤ (b : ℝ) := by exact_mod_cast hb
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hb₁ hn)) hH

end TauCeti
