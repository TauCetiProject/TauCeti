/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating complementary power bounds

A singular integrand can have two useful estimates: a power integrable at zero, and a power
integrable at infinity. Splitting at an arbitrary positive scale gives a bound independent of
the upper integration endpoint. This is useful for Hölder estimates of heat potentials, where
the scale is the square of the spatial separation.
-/

public section

namespace TauCeti

open MeasureTheory Set Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrate two complementary power bounds by splitting at `d`. The first power is integrable
at zero and the second at infinity; the resulting bound is uniform in the endpoint `t ≥ 0`. -/
theorem norm_intervalIntegral_le_of_rpow_bounds {f : ℝ → F} {a b A B d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d) (ht : 0 ≤ t)
    (hf : IntervalIntegrable f volume 0 t)
    (hnear : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ A * r ^ (a - 1))
    (hfar : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ B * r ^ (-b - 1)) :
    ‖∫ r in 0..t, f r‖ ≤ A / a * d ^ a + B / b * d ^ (-b) := by
  have hnear' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ A * r ^ (a - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hnear
  have hfar' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ B * r ^ (-b - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hfar
  have hsmall {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
      ‖∫ r in 0..s, f r‖ ≤ A / a * s ^ a := by
    have hr : -1 < a - 1 := by linarith
    calc
      ‖∫ r in 0..s, f r‖ ≤ ∫ r in 0..s, A * r ^ (a - 1) :=
        intervalIntegral.norm_integral_le_of_norm_le hs
          (hnear'.mono fun r hr hrs => hr ⟨hrs.1, hrs.2.trans hst⟩)
          ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul A)
      _ = A / a * s ^ a := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr)]
        simp [Real.zero_rpow ha.ne', sub_add_cancel, div_eq_mul_inv, mul_comm,
          mul_left_comm]
  by_cases htd : t ≤ d
  · exact (hsmall ht le_rfl).trans <| le_add_of_le_of_nonneg
      (mul_le_mul_of_nonneg_left (rpow_le_rpow ht htd ha.le) (div_nonneg hA ha.le))
      (by positivity)
  · have hdt : d ≤ t := (lt_of_not_ge htd).le
    have hp : ∀ r ∈ uIcc d t, r ≠ (0 : ℝ) := by
      intro r hr
      rw [uIcc_of_le hdt] at hr
      exact (hd.trans_le hr.1).ne'
    have htail : ‖∫ r in d..t, f r‖ ≤ B / b * d ^ (-b) := by
      calc
        ‖∫ r in d..t, f r‖ ≤ ∫ r in d..t, B * r ^ (-b - 1) :=
          intervalIntegral.norm_integral_le_of_norm_le hdt
            (hfar'.mono fun r hr hrs => hr ⟨hd.trans hrs.1, hrs.2⟩)
            (((continuousOn_id.rpow_const (fun r hr => Or.inl (hp r hr))).intervalIntegrable)
              |>.const_mul B)
        _ = B / b * (d ^ (-b) - t ^ (-b)) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inr ⟨by linarith, fun h => hp 0 h rfl⟩)]
          simp only [sub_add_cancel]
          field_simp
          ring
        _ ≤ B / b * d ^ (-b) := by
          exact mul_le_mul_of_nonneg_left (sub_le_self _ (rpow_nonneg ht _))
            (div_nonneg hB hb.le)
    have hfd : IntervalIntegrable f volume 0 d := hf.mono_set (by
      rw [uIcc_of_le hd.le, uIcc_of_le ht]
      exact Icc_subset_Icc le_rfl hdt)
    have hft : IntervalIntegrable f volume d t := hf.mono_set (by
      rw [uIcc_of_le hdt, uIcc_of_le ht]
      exact Icc_subset_Icc hd.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hfd hft]
    exact (norm_add_le _ _).trans (add_le_add (hsmall hd.le hdt) htail)

end TauCeti
