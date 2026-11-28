/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Bochner integrals and finite `Lᵖ` norms

For finite `Lᵖ` spaces `PiLp p E` (`1 ≤ p ≤ ∞`) with real normed fibers `E i` and integrable
coordinate functions `f i : Ω → E i`, Bochner–Minkowski gives
`‖WithLp.toLp p (fun i ↦ ∫ t, f i t ∂μ)‖ ≤ ∫ t, ‖WithLp.toLp p (fun i ↦ f i t)‖ ∂μ`
(`TauCeti.norm_toLp_integral_le`). We also record the weighted norm bound
`TauCeti.norm_toLp_integral_weighted_le` for maps `f : Ω → PiLp p β` with seminormed fibers and
a.e.-measurable coordinate norms bounded a.e. by `M ≥ 0`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- Bochner–Minkowski integral inequality for `PiLp p`: for `1 ≤ p ≤ ∞`, real normed fibers `E i`,
and integrable coordinate functions `f i`, the `PiLp` norm of the coordinatewise Bochner integral is
at most the Bochner integral of the `PiLp` norm. -/
theorem norm_toLp_integral_le {Ω ι : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (f : ∀ i, Ω → E i) (hf : ∀ i, Integrable (f i) μ) :
    ‖WithLp.toLp p (fun i ↦ ∫ t, f i t ∂μ)‖ ≤ ∫ t, ‖WithLp.toLp p (fun i ↦ f i t)‖ ∂μ := by
  let F : Ω → PiLp p (fun _ : ι ↦ ℝ) := fun t ↦ WithLp.toLp p (fun i ↦ ‖f i t‖)
  have hF : WithLp.toLp p (fun i ↦ ∫ t, ‖f i t‖ ∂μ) = ∫ t, F t ∂μ := PiLp.ext fun i ↦ by
    rw [PiLp.toLp_apply, MeasureTheory.eval_integral_piLp (fun i ↦ (hf i).norm) i]
  calc ‖WithLp.toLp p (fun i ↦ ∫ t, f i t ∂μ)‖
      = ‖WithLp.toLp p (fun i ↦ ‖WithLp.toLp p (fun j ↦ ∫ t, f j t ∂μ) i‖)‖ :=
        (PiLp.norm_norm _).symm
    _ ≤ ‖∫ t, F t ∂μ‖ := hF ▸ PiLp.norm_mono fun i ↦ by
        rw [PiLp.toLp_apply, PiLp.toLp_apply, norm_norm,
          Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖F t‖ ∂μ := norm_integral_le_integral_norm F
    _ = ∫ t, ‖WithLp.toLp p (fun i ↦ f i t)‖ ∂μ := integral_congr_ae (ae_of_all _ fun t ↦
        PiLp.norm_norm (WithLp.toLp p (fun i ↦ f i t)))

/-- Weighted integral norm bound in `PiLp`: for `1 ≤ p ≤ ∞`, seminormed fibers `β i`, a map
`f : Ω → PiLp p β` with a.e.-measurable coordinate norms satisfying `‖f t‖ ≤ M` almost everywhere,
and an a.e.-nonnegative integrable weight `w` of total mass `∫ t, w t ∂μ = α > 0`,
`‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ M`. -/
theorem norm_toLp_integral_weighted_le {Ω ι : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    (f : Ω → PiLp p β) (hf : ∀ i, AEMeasurable (fun t ↦ ‖f t i‖) μ) {M : ℝ}
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) {w : Ω → ℝ} {α : ℝ} (hα : 0 < α) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ t, w t ∂μ = α) :
    ‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ M := by
  let w' : Ω → ℝ := fun t ↦ max (w t) 0
  have hw' : w =ᵐ[μ] w' := hw_nonneg.mono fun _ ht ↦ (max_eq_left ht).symm
  have hw'_int : Integrable w' μ := hw_int.congr hw'
  have hint_eq (i : ι) : ∫ t, ‖f t i‖ * w t ∂μ = ∫ t, ‖f t i‖ * w' t ∂μ :=
    integral_congr_ae (hw'.mono fun _ ht ↦ by dsimp only; rw [ht])
  simp_rw [hint_eq]
  have hint (i : ι) : Integrable (fun t ↦ ‖f t i‖ * w' t) μ :=
    hw'_int.bdd_mul (hf i).aestronglyMeasurable (hfM.mono fun t ht ↦
      Real.norm_of_nonneg (norm_nonneg (f t i)) ▸ (PiLp.norm_apply_le (f t) i).trans ht)
  rw [show WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w' t ∂μ) =
      α⁻¹ • WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w' t ∂μ) from PiLp.ext fun _ ↦ by simp,
    norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le]
  calc α⁻¹ * ‖WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w' t ∂μ)‖
      ≤ α⁻¹ * ∫ t, ‖WithLp.toLp p (fun i ↦ ‖f t i‖ * w' t)‖ ∂μ :=
        mul_le_mul_of_nonneg_left (norm_toLp_integral_le _ hint) (inv_pos.2 hα).le
    _ ≤ α⁻¹ * ∫ t, M * w' t ∂μ := mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
        (ae_of_all _ fun _ ↦ norm_nonneg _) (hw'_int.const_mul M) (hfM.mono fun t ht ↦ by
          dsimp only; rw [show WithLp.toLp p (fun i ↦ ‖f t i‖ * w' t) =
            w' t • WithLp.toLp p (fun i ↦ ‖f t i‖) from PiLp.ext fun _ ↦ by simp [mul_comm],
            norm_smul, Real.norm_of_nonneg (le_max_right _ _), PiLp.norm_norm (f t), mul_comm]
          exact mul_le_mul_of_nonneg_right ht (le_max_right _ _))) (inv_pos.2 hα).le
    _ = M := by
        rw [integral_const_mul, (integral_congr_ae hw'.symm).trans hw_sum, mul_comm M,
          inv_mul_cancel_left₀ hα.ne']

end TauCeti
