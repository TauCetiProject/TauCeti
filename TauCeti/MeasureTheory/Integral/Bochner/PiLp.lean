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
(`TauCeti.norm_toLp_integral_le`).
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
    _ ≤ ‖WithLp.toLp p (fun i ↦ ∫ t, ‖f i t‖ ∂μ)‖ := PiLp.norm_mono fun i ↦ by
        rw [PiLp.toLp_apply, PiLp.toLp_apply, norm_norm,
          Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
        exact norm_integral_le_integral_norm _
    _ = ‖∫ t, F t ∂μ‖ := by rw [hF]
    _ ≤ ∫ t, ‖F t‖ ∂μ := norm_integral_le_integral_norm F
    _ = ∫ t, ‖WithLp.toLp p (fun i ↦ f i t)‖ ∂μ := integral_congr_ae (ae_of_all _ fun t ↦ by
        simpa only [F, PiLp.toLp_apply] using PiLp.norm_norm (WithLp.toLp p (fun i ↦ f i t)))

end TauCeti
