/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.HalfPlane

/-!
# A vertical bound for the real archimedean factor

On a closed strip in the right half-plane, the real archimedean factor absorbs a factor
of linear growth in the norm of the argument.
-/

public section

open Complex

namespace TauCeti.Complex

/-- `Γ_ℝ(z)` is bounded by a strip-dependent constant times `(1 + ‖z‖)⁻¹` on a closed
vertical strip strictly to the right of zero. -/
theorem exists_norm_Gammaℝ_mul_one_add_norm_le_of_re_mem_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖Gammaℝ z‖ * (1 + ‖z‖) ≤ C := by
  let B (x : ℝ) := Real.pi ^ (-x / 2) * (x / 2 + 2) ^ (x / 2 + 2)
  have hcont : ContinuousOn B (Set.Icc a b) := by
    apply (continuous_const.rpow (by fun_prop) (fun _ ↦ Or.inl Real.pi_pos.ne')).continuousOn.mul
    exact (by fun_prop : Continuous fun x : ℝ ↦ x / 2 + 2).continuousOn.rpow
      (by fun_prop) (fun x hx ↦ Or.inl (by linarith [hx.1] : x / 2 + 2 ≠ 0))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨2 * max 1 M * (1 + a⁻¹), by positivity, fun z hz ↦ ?_⟩
  have hz0 : 0 < ‖z‖ := ha.trans_le (hz.1.trans (re_le_norm z))
  have hg := norm_Gamma_le_re_add_two_rpow_div (z := z / 2)
    (by rw [div_ofNat_re]; linarith [hz.1])
  rw [div_ofNat_re, norm_div, norm_ofNat] at hg
  have hB : ‖Gammaℝ z‖ * ‖z‖ ≤ 2 * max 1 M := by
    rw [norm_Gammaℝ]
    calc
      _ ≤ (Real.pi ^ (-z.re / 2) * ((z.re / 2 + 2) ^ (z.re / 2 + 2) / (‖z‖ / 2))) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hz0.le
      _ = 2 * B z.re := by dsimp only [B]; field_simp
      _ ≤ _ := by linarith [(le_abs_self _).trans ((hM z.re hz).trans (le_max_right 1 M))]
  have hzA : ‖z‖⁻¹ ≤ a⁻¹ := inv_anti₀ ha (hz.1.trans (re_le_norm z))
  calc
    _ = ‖Gammaℝ z‖ * ‖z‖ * (1 + ‖z‖⁻¹) := by field_simp; ring
    _ ≤ _ := mul_le_mul hB (add_le_add_right hzA _) (by positivity) (by positivity)

end TauCeti.Complex
