/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lᵖ` convergence gives `L¹` convergence on a finite measure space

On a finite measure space, Mathlib's exponent comparison
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` bounds the `L¹` seminorm by the `Lᵖ` seminorm (for
`1 ≤ p`) times a finite constant. This file packages that comparison as a convergence statement
whose conclusion is the Bochner integral `∫ ‖f i‖ ∂μ`, the form in which `L¹` convergence of a
difference `f i = W i - a` is usually consumed.

It also contains the comparison of seminorms of exponents related by `1 / s = r / p` for pointwise
bounds `‖u‖ ≤ ‖f‖ ^ r`.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_rpow`: if `‖u‖ ≤ ‖f‖ ^ r`, then `‖u‖_s ≤ ‖f‖_p ^ r` when
  `1 / s = r / p`.
* `TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one`: its form for Hölder conjugate exponents.

* `TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm`: if `eLpNorm (f i) p μ → 0`
  for some `1 ≤ p`, then `∫ ‖f i‖ ∂μ → 0`.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

section Rpow

variable {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- If `‖u‖ ≤ ‖f‖ ^ r` almost everywhere with `r ≥ 0`, then `‖u‖_s ≤ ‖f‖_p ^ r` for the exponent
`1 / s = r / p`. For `r = 0` this reads `‖u‖_∞ ≤ 1`. -/
theorem eLpNorm_le_eLpNorm_rpow {f : α → E} {u : α → F} {p s : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r)
    (hf : AEStronglyMeasurable f μ) (hu : AEStronglyMeasurable u μ)
    (hs : s⁻¹ = ENNReal.ofReal r * p⁻¹) (hle : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖ ^ r) :
    eLpNorm u s μ ≤ eLpNorm f p μ ^ r := by
  rcases hr.eq_or_lt with rfl | hr
  · have hs : s = ∞ := by simpa using hs
    subst hs
    rw [ENNReal.rpow_zero, eLpNorm_exponent_top hu]
    simpa using eLpNormEssSup_le_of_ae_bound (C := 1) (by simpa using hle)
  · calc eLpNorm u s μ ≤ eLpNorm (fun x => ‖f x‖ ^ r) s μ := eLpNorm_mono_ae_real hu hle
      _ = eLpNorm f (s * ENNReal.ofReal r) μ ^ r := eLpNorm_norm_rpow f hf hr
      _ = eLpNorm f p μ ^ r := by
        congr 2
        have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
        rw [← inv_inv s, hs, ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top), inv_inv,
          mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- If `‖g‖ ≤ ‖f‖ ^ (q - 1)` almost everywhere, then `‖g‖_{q'} ≤ ‖f‖_q ^ (q - 1)` for Hölder
conjugate exponents `q < ∞` and `q'`. -/
theorem eLpNorm_le_eLpNorm_rpow_toReal_sub_one {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    (hq : q ≠ ∞) {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hle : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖ ^ (q.toReal - 1)) :
    eLpNorm g q' μ ≤ eLpNorm f q μ ^ (q.toReal - 1) := by
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  refine eLpNorm_le_eLpNorm_rpow (by linarith) hf hg ?_ hle
  rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
    ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]

end Rpow

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`Lᵖ` convergence implies `L¹` convergence on a finite measure space.** If `1 ≤ p` and a
family `f` tends to `0` in `Lᵖ` along a filter `l`, then `∫ ‖f i‖` tends to `0` along `l`.
No measurability hypothesis is needed: `eLpNorm (f i) p μ` is finite eventually along `l`, which
forces `f i` to be a.e. strongly measurable. -/
theorem tendsto_integral_norm_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, ‖f i ω‖ ∂μ) l (𝓝 0) := by
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    rw [ENNReal.toReal_one, sub_nonneg]
    gcongr
    simpa using ENNReal.toReal_mono hp_top hp
  have hL1 : Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
      fun _ => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp one_pos
    simpa using ENNReal.Tendsto.mul_const h
      (.inr (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ Set.univ)))
  have hreal : Tendsto (fun i => (eLpNorm (f i) 1 μ).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  refine hreal.congr' ?_
  filter_upwards [h.eventually_lt_const ENNReal.zero_lt_top] with i hi
  have hf := aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  rw [eLpNorm_one_eq_lintegral_enorm hf, integral_norm_eq_lintegral_enorm hf]

end MeasureTheory

end TauCeti
