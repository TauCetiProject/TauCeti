/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Folding Mellin integrals at a reciprocal symmetry point

The reflection `t ↦ a² / t` exchanges the two sides of a positive cutoff `a` and preserves
`dt / t`. The resulting folding identity `TauCeti.integral_multHaar_eq_two_smul_of_sq_div`
lets us bound a Mellin transform on the imaginary axis using only the upper tail of its norm.

For a normalized Dirichlet theta series the symmetry point is `a = 1 / √q`, and the
Mellin parameter on the critical line is `s - 1/2`. This is the normalization of
`New.integral_norm_thetaSeries_div` in the shorter GRH formalization
(<https://github.com/lsernau/grh-lean>, revision `72fead1`, `Lib/Analytic/DirichletTheta`).
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- A function with reciprocal symmetry in norm has an absolutely convergent Mellin transform
on the imaginary axis if its norm is integrable against `dt / t` above the symmetry point.
At any smaller cutoff, twice the tail integral of the norm bounds the transform. -/
theorem mellinConvergent_and_norm_mellin_le_of_sq_div {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} {z : ℂ}
    (hba : b ≤ a) (hz : z.re = 0) (hf : AEStronglyMeasurable f multHaar)
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), ‖f (a ^ 2 / t)‖ = ‖f t‖)
    (htail : IntegrableOn (fun t ↦ ‖f t‖) (Ioi b) multHaar) :
    MellinConvergent f z ∧ ‖mellin f z‖ ≤ 2 * ∫ t in Ioi b, ‖f t‖ ∂multHaar := by
  have hnorm := (integrable_multHaar_iff_of_sq_div hsym).mpr
    (htail.mono_set (Ioi_subset_Ioi hba))
  have heq : (fun t : ℝ ↦ ‖(t : ℂ) ^ z • f t‖) =ᵐ[multHaar] fun t ↦ ‖f t‖ := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, hz, Real.rpow_zero, one_mul]
  refine ⟨integrable_multHaar_cpow_smul_iff.mp ?_, ?_⟩
  · have hmeas : Measurable (fun t : ℝ ↦ (t : ℂ) ^ z) := by fun_prop
    exact (integrable_norm_iff (hmeas.aestronglyMeasurable.smul hf)).mp (hnorm.congr heq.symm)
  · rw [← integral_multHaar_cpow_smul]
    calc
      _ ≤ ∫ t, ‖(t : ℂ) ^ z • f t‖ ∂multHaar := norm_integral_le_integral_norm _
      _ ≤ 2 * ∫ t in Ioi a, ‖f t‖ ∂multHaar := by
        rw [integral_congr_ae heq]
        by_cases ha : 0 < a
        · rw [integral_multHaar_eq_two_smul_of_sq_div ha hsym, two_nsmul, two_mul]
        · rw [multHaar_restrict_Ioi_of_nonpos (le_of_not_gt ha)]
          exact le_mul_of_one_le_left (integral_nonneg fun _ ↦ norm_nonneg _) one_le_two
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set htail (ae_of_all _ fun _ ↦ norm_nonneg _)
          (Filter.Eventually.of_forall (Ioi_subset_Ioi hba))) zero_le_two

end TauCeti
