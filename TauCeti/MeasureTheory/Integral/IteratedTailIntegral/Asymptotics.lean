/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Tail asymptotics of iterated improper tail integrals

This file records asymptotic integrability and decay bounds for `TauCeti.iteratedTailIntegral`
that do not depend on oscillatory cancellation.

## Main results

* `TauCeti.integrableOn_Ioi_and_isBigO_iteratedTailIntegral_one_of_isBigO_rpow`: a function
  `g : ℝ → E` locally integrable on `[a, ∞)` with `g =O[atTop] fun t ↦ t ^ (-M)` (`1 < M`) is
  Bochner integrable on `(a, ∞)`, and its first tail integral satisfies
  `iteratedTailIntegral g 1 =O[atTop] fun x ↦ x ^ (-B)` for every `B ≤ M - 1`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set

/-- Integrability and tail `O(x ^ (-B))` bound for a locally integrable function `g = O(t ^ (-M))`
with `1 < M` and `B ≤ M - 1`. -/
theorem integrableOn_Ioi_and_isBigO_iteratedTailIntegral_one_of_isBigO_rpow
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} {a B M : ℝ} (hg_loc : LocallyIntegrableOn g (Ici a))
    (hM : 1 < M) (hBM : B ≤ M - 1) (hg : g =O[atTop] fun t : ℝ ↦ t ^ (-M)) :
    IntegrableOn g (Ioi a) ∧
      iteratedTailIntegral g 1 =O[atTop] fun x : ℝ ↦ x ^ (-B) := by
  obtain ⟨C, _, hC⟩ := hg.exists_nonneg
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hC.bound
  let x₁ : ℝ := max (max a 1) R₀
  have hx₁_pos : 0 < x₁ := lt_of_lt_of_le zero_lt_one ((le_max_right a 1).trans (le_max_left _ _))
  have ha_x₁ : a ≤ x₁ := (le_max_left a 1).trans (le_max_left _ _)
  have hmaj {y : ℝ} (hy : 0 < y) : IntegrableOn (fun t : ℝ ↦ C * t ^ (-M)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -M < -1) hy).const_mul C
  have hint_a : IntegrableOn g (Ioi a) :=
    (hg_loc.integrableOn_of_isBigO_atTop hg
      (integrableAtFilter_rpow_atTop_iff.mpr (by linarith))).mono_set Ioi_subset_Ici_self
  have htail : iteratedTailIntegral g 1 =O[atTop] fun x : ℝ ↦ x ^ (-(M - 1)) := by
    refine isBigO_iff.mpr ⟨C / (M - 1), ?_⟩
    filter_upwards [eventually_ge_atTop x₁] with x hx
    have hx_pos : 0 < x := hx₁_pos.trans_le hx
    have hint_x : IntegrableOn g (Ioi x) := hint_a.mono_set (Ioi_subset_Ioi (ha_x₁.trans hx))
    rw [iteratedTailIntegral_one_eq_integral_Ioi hint_x,
      Real.norm_of_nonneg (Real.rpow_nonneg hx_pos.le _)]
    calc
      ‖∫ t in Ioi x, g t‖ ≤ ∫ t in Ioi x, ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi x, C * t ^ (-M) :=
            setIntegral_mono_on hint_x.norm (hmaj hx_pos) measurableSet_Ioi fun t (ht : x < t) ↦ by
              simpa [Real.norm_of_nonneg (Real.rpow_nonneg (hx_pos.trans ht).le _)] using
                hR₀ t ((le_max_right _ _).trans (hx.trans ht.le))
      _ = (C / (M - 1)) * x ^ (-(M - 1)) := by
            have hexp : -M + 1 = -(M - 1) := by ring
            rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -M < -1) hx_pos, hexp]
            have hne : M - 1 ≠ 0 := by linarith
            field_simp [hne]
  exact ⟨hint_a, htail.trans (isBigO_rpow_rpow_atTop_of_le (neg_le_neg hBM))⟩

end TauCeti
