/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential sums from cumulative bounds

A bound on the total weight of the indices with `d i ≤ u` gives a bound on the
sum of the weights against `exp (-L * d i)`. The exponential kernel integrates
this cumulative weight starting at any common lower bound for the `d i`.
-/

public section

open MeasureTheory Real Set

namespace Finset

/-- If the cumulative weight up to `u` is at most `C * exp (A * u)` above the common lower
edge `g`, then the Laplace sum at `L > max 0 A` decays as `exp (-(L - A) * g)`.
The individual weights need not be nonnegative. -/
theorem sum_mul_exp_neg_mul_le_of_cumulative_le (s : Finset ι) (d w : ι → ℝ)
    {L A C g : ℝ} (hL : 0 < L) (hLA : A < L) (hg : ∀ i ∈ s, g ≤ d i)
    (hcount : ∀ u > g, (∑ i ∈ s.filter (fun i ↦ d i ≤ u), w i) ≤ C * exp (A * u)) :
    ∑ i ∈ s, w i * exp (-L * d i) ≤ C * (L / (L - A)) * exp (-(L - A) * g) := by
  let f (i : ι) : ℝ → ℝ := (Set.Ici (d i)).indicator (fun u ↦ (w i * L) * exp (-L * u))
  have hi (i : ι) : Integrable (f i) :=
    (integrable_indicator_iff measurableSet_Ici).2 <|
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hL) (d i)).congr_set_ae
        Ioi_ae_eq_Ici.symm).const_mul _
  have hterm (i) (hi' : i ∈ s) : (∫ u in Set.Ioi g, f i u) = w i * exp (-L * d i) := by
    rw [← integral_Ici_eq_integral_Ioi]
    simp only [f]
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, max_eq_right (hg i hi'),
      integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hL)]
    field_simp
  have hrate : A - L < 0 := sub_neg.mpr hLA
  have hmajor : IntegrableOn (fun u ↦ (C * L) * exp ((A - L) * u)) (Set.Ioi g) :=
    (integrableOn_exp_mul_Ioi hrate g).const_mul _
  calc
    _ = ∫ u in Set.Ioi g, ∑ i ∈ s, f i u := by
      rw [integral_finsetSum s (fun i _ ↦ (hi i).integrableOn)]
      exact Finset.sum_congr rfl fun i hi' ↦ (hterm i hi').symm
    _ ≤ ∫ u in Set.Ioi g, (C * L) * exp ((A - L) * u) := by
      refine setIntegral_mono_on (integrable_finsetSum s fun i _ ↦ (hi i).integrableOn)
        hmajor measurableSet_Ioi fun u hu ↦ ?_
      have hsum : (∑ i ∈ s, f i u) =
          (∑ i ∈ s.filter (fun i ↦ d i ≤ u), w i) * (L * exp (-L * u)) := by
        rw [Finset.sum_mul, Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ ↦ by
          by_cases h : d i ≤ u <;> simp [f, h, mul_assoc]
      rw [hsum]
      calc
        _ ≤ (C * exp (A * u)) * (L * exp (-L * u)) :=
          mul_le_mul_of_nonneg_right (hcount u hu) (by positivity)
        _ = _ := by rw [mul_mul_mul_comm C, ← exp_add]; ring_nf
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hrate]
      have hsub : A - L = -(L - A) := by ring
      rw [hsub, neg_div_neg_eq]
      ring

end Finset
