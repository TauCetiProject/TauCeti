/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.MellinTransform.Growth
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Mellin transforms with a positive cutoff

Removing a neighbourhood of zero makes the Mellin transform of a locally integrable,
exponentially decaying kernel entire. On the imaginary axis its norm is controlled by the
unweighted tail mass for `dt / t` by `TauCeti.norm_mellin_indicator_Ioi_le_integral_rpow_mul_norm`
in `TauCeti.Analysis.MellinTransform.Basic`. On a closed strip to the right of that axis, only
`t > 1` needs a higher moment. The estimates keep the tail mass explicit, so that a bound on
that mass can be used as a boundary estimate in the three-lines theorem.

This is the analytic step for the truncated theta mollifier in
`New.mollifier` and `New.three_lines_bound_of_LFunction_eq_zero` of the shorter formal proof
(lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`). In the normalization
`θ(t) = √t ∑ₙ c(n) w(nt)`, the mollifier is the truncated Mellin transform of `θ` at `s - 1/2`,
so its critical-line bound uses the estimate at `Re (s - 1/2) = 0`.
-/

public section

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- A positive cutoff kills the kernel at zero and leaves its exponential decay unchanged. -/
private theorem mellin_indicator_Ioi_bounds {f : ℝ → E} {r c : ℝ} (hr : 0 < r)
    (hf : LocallyIntegrableOn f (Ici r)) (hdecay : f =O[atTop] fun t ↦ Real.exp (-c * t))
    (b : ℝ) :
    LocallyIntegrableOn ((Ioi r).indicator f) (Ioi 0) ∧
      (Ioi r).indicator f =O[atTop] (fun t ↦ Real.exp (-c * t)) ∧
      (Ioi r).indicator f =O[𝓝[>] 0] (· ^ (-b)) := by
  refine ⟨(hf.mono_set (by rw [closure_Ioi]; exact inter_subset_right)).indicator_of_closure
    measurableSet_Ioi.nullMeasurableSet, hdecay.congr' ?_ EventuallyEq.rfl, ?_⟩
  · filter_upwards [eventually_gt_atTop r] with t ht
    exact (indicator_of_mem ht f).symm
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    exact (indicator_of_notMem ht.2.not_gt f).symm

/-- The Mellin integral above a positive cutoff is absolutely convergent at every complex
argument if the kernel is locally integrable up to the cutoff and decays exponentially. -/
theorem mellinConvergent_indicator_Ioi_of_isBigO_exp {f : ℝ → E} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hf : LocallyIntegrableOn f (Ici r))
    (hdecay : f =O[atTop] fun t ↦ Real.exp (-c * t)) (s : ℂ) :
    MellinConvergent ((Ioi r).indicator f) s := by
  obtain ⟨hloc, htop, hbot⟩ := mellin_indicator_Ioi_bounds hr hf hdecay (s.re - 1)
  exact mellinConvergent_of_isBigO_rpow_exp hc hloc htop hbot (sub_one_lt _)

/-- The Mellin transform above a positive cutoff is entire if the kernel is locally integrable
up to the cutoff and decays exponentially. -/
theorem differentiable_mellin_indicator_Ioi_of_isBigO_exp {f : ℝ → E} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hf : LocallyIntegrableOn f (Ici r))
    (hdecay : f =O[atTop] fun t ↦ Real.exp (-c * t)) :
    Differentiable ℂ (mellin ((Ioi r).indicator f)) := by
  intro s
  obtain ⟨hloc, htop, hbot⟩ := mellin_indicator_Ioi_bounds hr hf hdecay (s.re - 1)
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc hloc htop hbot (sub_one_lt _)

/-- For `0 ≤ Re s ≤ R`, bound a truncated Mellin transform by its absolute mass on the
imaginary axis plus a Gamma moment of the exponential majorant above `1`. In applications
where the cutoff tends to zero, the Gamma term is independent of the cutoff. -/
theorem norm_mellin_indicator_Ioi_le_add_of_norm_le_exp_neg_mul_rpow
    {f : ℝ → E} {r C c α R : ℝ} (hr : 0 ≤ r) (hc : 0 < c) (hα : 0 < α)
    (hf : IntegrableOn (fun t ↦ ‖f t‖ / t) (Ioi r))
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ C * Real.exp (-c * t ^ α))
    {s : ℂ} (hs : 0 ≤ s.re) (hsR : s.re ≤ R) :
    ‖mellin ((Ioi r).indicator f) s‖ ≤ (∫ t in Ioi r, ‖f t‖ / t) +
      C * (c ^ (-(R + 1) / α) * Real.Gamma ((R + 1) / α) / α) := by
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans
    (hbound 2 (by norm_num))) (Real.exp_pos _)
  have hmoment := integrableOn_rpow_mul_exp_neg_mul_rpow_div (R := R) hc hα
  have hmajor : Integrable ((Ioi (1 : ℝ)).indicator
      (fun u ↦ C * (u ^ R * Real.exp (-c * u ^ α) / u))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hmoment.const_mul C)
  rw [mellin_indicator_Ioi _ hr]
  calc
    _ ≤ ∫ t in Ioi r, ‖f t‖ / t + (Ioi (1 : ℝ)).indicator
        (fun u ↦ C * (u ^ R * Real.exp (-c * u ^ α) / u)) t := by
      refine norm_integral_le_of_norm_le (hf.add hmajor.integrableOn) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₀ : 0 < t := hr.trans_lt ht
      rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht₀, sub_re, one_re, Real.rpow_sub ht₀,
        Real.rpow_one]
      by_cases ht₁ : t ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem ht₁]
        have hp : t ^ s.re ≤ t ^ R := Real.rpow_le_rpow_of_exponent_le ht₁.le hsR
        have hle : t ^ s.re / t * ‖f t‖ ≤ C * (t ^ R * Real.exp (-c * t ^ α) / t) := by
          rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_left_comm C]
          exact div_le_div_of_nonneg_right (mul_le_mul hp (hbound t ht₁) (norm_nonneg _)
            (Real.rpow_nonneg ht₀.le _)) ht₀.le
        exact hle.trans (le_add_of_nonneg_left (by positivity))
      · rw [indicator_of_notMem ht₁, add_zero, div_mul_eq_mul_div]
        have hp : t ^ s.re ≤ 1 := Real.rpow_le_one (by positivity) (not_lt.mp ht₁) hs
        exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hp) ht₀.le
    _ ≤ _ := by
      rw [integral_add hf hmajor.integrableOn, setIntegral_indicator measurableSet_Ioi,
        integral_const_mul]
      gcongr
      refine (setIntegral_mono_set hmoment ?_ (Eventually.of_forall inter_subset_right)).trans ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu₀ : 0 < u := zero_lt_one.trans hu
        positivity
      · exact integral_rpow_mul_exp_neg_mul_rpow_div_le_Gamma (by linarith) hc hα

end TauCeti
