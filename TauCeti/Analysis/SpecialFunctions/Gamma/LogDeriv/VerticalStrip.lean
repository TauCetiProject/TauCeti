/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma

/-!
# Logarithmic growth of the real gamma logarithmic derivative

On a bounded vertical strip, away from the real axis, the real gamma logarithmic derivative
has logarithmic growth. This controls the archimedean term of Dirichlet logarithmic derivatives
on horizontal contours, including to the left of the imaginary axis.
-/

public section

namespace Complex

/-- A uniform logarithmic bound for the real gamma logarithmic derivative on `-1 ≤ Re s ≤ 3`
at heights of absolute value at least `1/2`. -/
theorem exists_norm_logDeriv_Gammaℝ_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Set.Icc (-1) 3 → 1 / 2 ≤ |s.im| →
      ‖logDeriv Gammaℝ s‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨D, hD, hψ⟩ := exists_norm_digamma_le_log (b := 5 / 2) (by norm_num : 0 < (1 / 2 : ℝ))
  let B := |Real.log Real.pi| / 2 + 2
  refine ⟨D / 2 + B / Real.log 2, by positivity, fun s hs him ↦ ?_⟩
  have hw : ((s + 2) / 2).re ∈ Set.Icc (1 / 2) (5 / 2) := by
    norm_num [div_ofNat_re, add_re]
    constructor <;> linarith [hs.1, hs.2]
  have hlog : Real.log (|((s + 2) / 2).im| + 2) ≤ Real.log (|s.im| + 2) := by
    norm_num [div_ofNat_im, add_im, abs_div]
    gcongr
    linarith [abs_nonneg s.im]
  have hne : Gammaℝ s ≠ 0 := by
    rintro hz
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hz
    have hi : s.im = 0 := by simpa using congrArg im hn
    rw [hi, abs_zero] at him
    linarith
  have hshift : Gammaℝ (s + 2) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith [hs.1])
  have hinv : ‖s⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_le_comm₀ (by linarith [abs_im_le_norm s]) (by norm_num)]
    simpa only [one_div] using him.trans (abs_im_le_norm s)
  have hbase : Real.log 2 ≤ Real.log (|s.im| + 2) := by gcongr; linarith [abs_nonneg s.im]
  have hbase₀ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : B ≤ (B / Real.log 2) * Real.log (|s.im| + 2) := by
    calc B = (B / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hbase₀.ne').symm
         _ ≤ _ := by gcongr
  have heq : logDeriv Gammaℝ s = logDeriv Gammaℝ (s + 2) - s⁻¹ :=
    eq_sub_of_add_eq (logDeriv_Gammaℝ_add_two hne).symm
  rw [heq, logDeriv_Gammaℝ (fun n hn ↦ hshift (Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩))]
  calc
    _ ≤ ‖digamma ((s + 2) / 2)‖ / 2 + |Real.log Real.pi| / 2 + ‖s⁻¹‖ := by
      let u := digamma ((s + 2) / 2) / 2
      let v := (Real.log Real.pi : ℂ) / 2
      simpa only [u, v, norm_div, norm_ofNat, norm_real, Real.norm_eq_abs] using
        (norm_sub_le (u - v) s⁻¹).trans (add_le_add_left (norm_sub_le u v) _)
    _ ≤ D * Real.log (|s.im| + 2) / 2 + B := by
      have hp := (hψ _ hw).trans (mul_le_mul_of_nonneg_left hlog hD.le)
      dsimp [B]
      linarith only [hp, hinv]
    _ ≤ _ := by rw [add_mul]; linarith only [hB]

end Complex
