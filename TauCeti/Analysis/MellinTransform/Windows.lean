/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.MellinTransform.Basic

/-!
# One-sided Mellin bounds on windows

The weighted positive-part integral on `[Y, Y ^ L]` becomes an exponentially weighted
integral on `[U, L * U]` under `Y = exp U`, by `TauCeti.intervalIntegral_mul_exp_comp_exp`. A
pointwise power bound on arbitrarily far-out windows implies a subpower bound for the
positive-part integrals on such windows. These are the two forms of localization needed to
pass from Laplace to Mellin criteria.
-/

public section

open Filter MeasureTheory Set
open scoped Interval

namespace TauCeti

/-- Subpower bounds on arbitrarily far-out Mellin windows are equivalent to subexponential
bounds on their logarithmic windows. -/
theorem frequently_integral_mul_rpow_le_rpow_iff (g : ℝ → ℝ) (L θ η : ℝ) :
    (∃ᶠ Y in atTop, (∫ y in Y..(Y ^ L), g y * y ^ (-(θ + 1))) ≤ Y ^ η) ↔
      ∃ᶠ U in atTop, (∫ u in U..(L * U), g (Real.exp u) * Real.exp (-θ * u)) ≤
        Real.exp (η * U) := by
  nth_rw 1 [← Real.map_exp_atTop]
  rw [frequently_map]
  refine frequently_congr (Eventually.of_forall fun U ↦ ?_)
  rw [intervalIntegral_mul_exp_comp_exp g, mul_comm L U, mul_comm η U, Real.exp_mul,
    Real.exp_mul]

/-- An upper power bound on arbitrarily far-out scale windows gives arbitrarily far-out windows
on which the weighted positive-part integral is at most `Y ^ η`, for any `η > 0`. -/
theorem HasWindows.frequently_integral_mul_rpow_le_rpow {G : ℝ → ℝ} {L C θ η : ℝ}
    (h : HasWindows {y | G y ≤ C * y ^ θ} L) (hη : 0 < η) :
    ∃ᶠ Y in atTop, (∫ y in Y..(Y ^ L), max (G y) 0 * y ^ (-(θ + 1))) ≤ Y ^ η := by
  rw [frequently_integral_mul_rpow_le_rpow_iff (fun y ↦ max (G y) 0)]
  have hsmall : ∀ᶠ U : ℝ in atTop, max C 0 * (L - 1) * U ≤ Real.exp (η * U) := by
    simpa only [Real.rpow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      using (((isLittleO_rpow_exp_pos_mul_atTop 1 hη).const_mul_left (max C 0 * (L - 1))).bound
        one_pos).mono (fun _ hu ↦ (le_abs_self _).trans hu)
  refine ((hasWindows_iff_frequently_exp.mp h).and_eventually hsmall).mono ?_
  rintro U ⟨⟨_, hU⟩, hsmallU⟩
  rcases le_total U (L * U) with hab | hba
  · rw [intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ _ in Ioc U (L * U), max C 0 := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun _ ↦ by positivity))
          (integrableOn_const (by simp))
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have huG : G (Real.exp u) ≤ C * Real.exp (u * θ) := by
          simpa only [mem_preimage, mem_ofPred_eq, ← Real.exp_mul] using
            hU (Ioc_subset_Icc_self hu)
        rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le, zero_mul]
        refine max_le_max ?_ le_rfl
        calc
          _ ≤ (C * Real.exp (u * θ)) * Real.exp (-θ * u) :=
            mul_le_mul_of_nonneg_right huG (Real.exp_pos _).le
          _ = C := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
      _ = max C 0 * (L - 1) * U := by
        rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul]
        ring
      _ ≤ _ := hsmallU
  · rw [intervalIntegral.integral_symm (L * U) U]
    exact (neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall hba
      fun _ ↦ by positivity)).trans (Real.exp_pos _).le

end TauCeti
