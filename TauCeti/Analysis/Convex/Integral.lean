/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Weighted logarithmic Jensen inequality

For an almost everywhere nonnegative integrable weight `w : Ω → ℝ` of positive total mass
`∫ s, w s ∂μ = α > 0` and an almost everywhere positive real integrand `u : Ω → ℝ` such that
`u * w` and `(Real.log ∘ u) * w` are integrable,
`α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ)`
(`MeasureTheory.inv_mul_integral_log_mul_le`).
-/

public section

namespace MeasureTheory

/-- **Weighted logarithmic Jensen inequality.** For an almost everywhere nonnegative integrable
weight `w : Ω → ℝ` with positive total mass `∫ s, w s ∂μ = α > 0`, and an almost everywhere
positive real integrand `u : Ω → ℝ` such that `s ↦ u s * w s` and `s ↦ Real.log (u s) * w s` are
integrable, `α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ)`. -/
theorem inv_mul_integral_log_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u w : Ω → ℝ} {α : ℝ} (hα : 0 < α) (hu_pos : ∀ᵐ s ∂μ, 0 < u s)
    (hw_int : Integrable w μ) (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α)
    (hu_int : Integrable (fun s ↦ u s * w s) μ)
    (hlog_int : Integrable (fun s ↦ Real.log (u s) * w s) μ) :
    α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ) := by
  have huw_nn : 0 ≤ᵐ[μ] fun s ↦ u s * w s :=
    hu_pos.mp (hw_nonneg.mono fun _ hw hu ↦ mul_nonneg hu.le hw)
  have hI : 0 < ∫ s, u s * w s ∂μ := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae huw_nn) fun h0 ↦ hα.ne' ?_
    have huw0 : (fun s ↦ u s * w s) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae huw_nn hu_int).1 h0.symm
    have hw0 : w =ᵐ[μ] 0 := huw0.mp (hu_pos.mono fun _ hu h ↦ (mul_eq_zero.1 h).resolve_left hu.ne')
    exact hw_sum.symm.trans (integral_eq_zero_of_ae hw0)
  set I := ∫ s, u s * w s ∂μ
  set c := α⁻¹ * I
  have hc : 0 < c := mul_pos (inv_pos.2 hα) hI
  have hpt : ∀ᵐ s ∂μ, Real.log (u s) * w s - Real.log c * w s ≤ c⁻¹ * (u s * w s) - w s := by
    filter_upwards [hu_pos, hw_nonneg] with s hus hws
    have hlog := (Real.log_le_sub_one_of_pos (div_pos hus hc)).trans_eq (by
      rw [div_eq_inv_mul])
    rw [Real.log_div hus.ne' hc.ne'] at hlog
    have := mul_le_mul_of_nonneg_right hlog hws
    linarith
  have hint : (∫ s, Real.log (u s) * w s ∂μ) - Real.log c * α ≤ c⁻¹ * I - α := by
    have h : (∫ s, (Real.log (u s) * w s - Real.log c * w s) ∂μ) ≤
        ∫ s, (c⁻¹ * (u s * w s) - w s) ∂μ :=
      integral_mono_ae (hlog_int.sub (hw_int.const_mul _))
        ((hu_int.const_mul _).sub hw_int) hpt
    rwa [integral_sub hlog_int (hw_int.const_mul _), integral_sub (hu_int.const_mul _) hw_int,
      integral_const_mul, integral_const_mul, hw_sum] at h
  have hcI : c⁻¹ * I = α := by
    dsimp [c]
    field_simp
  rw [hcI, sub_self, sub_nonpos, mul_comm (Real.log c) α] at hint
  exact (inv_mul_le_iff₀ hα).2 hint

end MeasureTheory
