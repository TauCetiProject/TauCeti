/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals of `Lᵖ` functions against bounded multipliers on finite-measure sets

If `h ∈ Lᵖ`, `1 ≤ p`, vanishes a.e. off a set `W` of finite measure and `k` is a scalar
multiplier a.e. bounded by `B` on `W`, then `k • h` is integrable and, by Hölder's
inequality on `W`,

`‖∫ k • h‖ ≤ B μ(W) ^ (1 - 1/p) ‖h‖_p`

(`TauCeti.integrable_smul_and_norm_integral_smul_le`). This is the estimate that makes
`h ↦ ∫ k • h` continuous on `Lᵖ` functions supported in `W`, used to pass to the limit in kernel
integrals `∫ K(x - y) h(y) dy` for `x` away from the support of `h`
(`TauCeti.tendsto_integral_smul_of_tendsto_eLpNorm_sub`).
-/

public section

namespace TauCeti

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If `k` is a.e. bounded by `B` on a set `W` of finite measure, and `h ∈ Lᵖ`, `1 ≤ p`,
vanishes a.e. off `W`, then `k • h` is integrable and, by Hölder's inequality on `W`,
`‖∫ k • h‖ ≤ B μ(W) ^ (1 - 1/p) ‖h‖_p`. -/
theorem integrable_smul_and_norm_integral_smul_le {k : α → ℝ} {W : Set α} (hμW : μ W ≠ ∞)
    {B : ℝ} (hB : 0 ≤ B) (hk : AEStronglyMeasurable k (μ.restrict W))
    (hkB : ∀ᵐ y ∂μ.restrict W, ‖k y‖ ≤ B) {p : ℝ≥0∞} (hp : 1 ≤ p) {h : α → F}
    (hh : MemLp h p μ) (h0 : ∀ᵐ y ∂μ, y ∉ W → h y = 0) :
    Integrable (fun y => k y • h y) μ ∧
      ‖∫ y, k y • h y ∂μ‖ ≤ B * (μ W ^ (1 - 1 / p.toReal) * eLpNorm h p μ).toReal := by
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hμW
  have hexp := zero_le_one_sub_one_div_toReal hp
  have hhW : IntegrableOn h W μ := (hh.restrict W).integrable hp
  have hbound : ∀ᵐ y ∂μ.restrict W, ‖k y • h y‖ ≤ B * ‖h y‖ := hkB.mono fun y hy => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hint : IntegrableOn (fun y => k y • h y) W μ :=
    (hhW.norm.const_mul B).mono' (hk.smul (hh.restrict W).aestronglyMeasurable) hbound
  have hkh0 : ∀ᵐ y ∂μ, y ∉ W → k y • h y = 0 := h0.mono fun y hy hyW => by simp [hy hyW]
  refine ⟨hint.integrable_of_ae_notMem_eq_zero hkh0, ?_⟩
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hkh0]
  refine (norm_integral_le_of_norm_le (hhW.norm.const_mul B) hbound).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hB
  rw [integral_norm_eq_lintegral_enorm (hh.restrict W).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm (hh.restrict W).aestronglyMeasurable]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hexp hμW)
    hh.eLpNorm_ne_top) ?_
  calc eLpNorm h 1 (μ.restrict W)
      ≤ eLpNorm h p (μ.restrict W) * μ.restrict W univ ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hh.restrict W).aestronglyMeasurable
    _ ≤ eLpNorm h p μ * μ W ^ (1 - 1 / p.toReal) := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
        gcongr
        exact Measure.restrict_le_self
    _ = _ := mul_comm _ _

/-- **Continuity of kernel integrals in `Lᵖ`.** Let `k` be a.e. bounded by `B` on a set `W` of
finite measure, and let `φ i` and `f` be in `Lᵖ`, `1 ≤ p`, and vanish a.e. off `W` (for `φ i`
eventually along `l`). If `φ i → f` in `Lᵖ`, then `∫ k • φ i → ∫ k • f`. -/
theorem tendsto_integral_smul_of_tendsto_eLpNorm_sub {ι : Type*} {l : Filter ι} {k : α → ℝ}
    {W : Set α} (hμW : μ W ≠ ∞) {B : ℝ} (hB : 0 ≤ B) (hk : AEStronglyMeasurable k (μ.restrict W))
    (hkB : ∀ᵐ y ∂μ.restrict W, ‖k y‖ ≤ B) {p : ℝ≥0∞} (hp : 1 ≤ p) {φ : ι → α → F} {f : α → F}
    (hφ : ∀ i, MemLp (φ i) p μ) (hf : MemLp f p μ)
    (hφ0 : ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ W → φ i y = 0) (hf0 : ∀ᵐ y ∂μ, y ∉ W → f y = 0)
    (hlim : Tendsto (fun i => eLpNorm (φ i - f) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ y, k y • φ i y ∂μ) l (𝓝 (∫ y, k y • f y ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hexp := zero_le_one_sub_one_div_toReal hp
  have hlim' : Tendsto (fun i => B * (μ W ^ (1 - 1 / p.toReal) * eLpNorm (φ i - f) p μ).toReal) l
      (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.rpow_ne_top_of_nonneg hexp hμW))
    rw [mul_zero] at h
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).const_mul B
  refine squeeze_zero_norm' ?_ hlim'
  filter_upwards [hφ0] with i hi
  obtain ⟨hint₁, -⟩ := integrable_smul_and_norm_integral_smul_le hμW hB hk hkB hp (hφ i) hi
  obtain ⟨hint₂, -⟩ := integrable_smul_and_norm_integral_smul_le hμW hB hk hkB hp hf hf0
  obtain ⟨-, hle⟩ := integrable_smul_and_norm_integral_smul_le hμW hB hk hkB hp ((hφ i).sub hf)
    ((hi.and hf0).mono fun y hy hyW => by simp [hy.1 hyW, hy.2 hyW])
  rw [norm_norm, ← integral_sub hint₁ hint₂]
  simp_rw [← smul_sub]
  exact hle

end TauCeti
