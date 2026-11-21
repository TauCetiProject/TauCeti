/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Integrals of squared norms

Two comparison bounds for the integrals `∫ ‖f‖²` of square-integrable functions, stated with the
integrals themselves rather than with `eLpNorm`, as they appear in energy estimates: the bound
`∫ ‖f₁ + f₂ + f₃‖² ≤ 3 (∫ ‖f₁‖² + ∫ ‖f₂‖² + ∫ ‖f₃‖²)`
(`MeasureTheory.integral_norm_sq_le_three_mul`) and the pointwise comparison
`‖f‖ ≤ c ‖g‖ ⟹ ∫ ‖f‖² ≤ c² ∫ ‖g‖²` (`MeasureTheory.integral_norm_sq_le_sq_mul_of_norm_le`), with
its instance for operators bounded by `c` applied to `f`
(`MeasureTheory.memLp_clm_apply_and_integral_norm_sq_le`); and the
almost everywhere convergent subsequence of a sequence with `∫ ‖f n - g‖² → 0`
(`MeasureTheory.exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq`), Riesz's theorem through
convergence in measure.
-/

public section

open Filter Topology

namespace MeasureTheory

/-- If `f = f₁ + f₂ + f₃` almost everywhere with `f₁, f₂, f₃ ∈ L²`, then
`∫ ‖f‖² ≤ 3 (∫ ‖f₁‖² + ∫ ‖f₂‖² + ∫ ‖f₃‖²)`. -/
theorem integral_norm_sq_le_three_mul {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f f₁ f₂ f₃ : α → E} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ)
    (h₃ : MemLp f₃ 2 μ) (hf : ∀ᵐ x ∂μ, f x = f₁ x + f₂ x + f₃ x) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤
      3 * (∫ x, ‖f₁ x‖ ^ 2 ∂μ + ∫ x, ‖f₂ x‖ ^ 2 ∂μ + ∫ x, ‖f₃ x‖ ^ 2 ∂μ) := by
  have i₁ := (memLp_two_iff_integrable_sq_norm h₁.aestronglyMeasurable).1 h₁
  have i₂ := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).1 h₂
  have i₃ := (memLp_two_iff_integrable_sq_norm h₃.aestronglyMeasurable).1 h₃
  have e : ∫ x, 3 * (‖f₁ x‖ ^ 2 + ‖f₂ x‖ ^ 2 + ‖f₃ x‖ ^ 2) ∂μ =
      3 * (∫ x, ‖f₁ x‖ ^ 2 ∂μ + ∫ x, ‖f₂ x‖ ^ 2 ∂μ + ∫ x, ‖f₃ x‖ ^ 2 ∂μ) := by
    have i₁₂ : Integrable (fun x ↦ ‖f₁ x‖ ^ 2 + ‖f₂ x‖ ^ 2) μ := i₁.add i₂
    rw [integral_const_mul, integral_add i₁₂ i₃, integral_add i₁ i₂]
  rw [← e]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    (((i₁.add i₂).add i₃).const_mul 3) ?_
  filter_upwards [hf] with x hx
  simp only [hx]
  have : ‖f₁ x + f₂ x + f₃ x‖ ≤ ‖f₁ x‖ + ‖f₂ x‖ + ‖f₃ x‖ := norm_add₃_le
  nlinarith [sq_nonneg (‖f₁ x‖ - ‖f₂ x‖), sq_nonneg (‖f₂ x‖ - ‖f₃ x‖),
    sq_nonneg (‖f₁ x‖ - ‖f₃ x‖), norm_nonneg (f₁ x + f₂ x + f₃ x), norm_nonneg (f₁ x),
    norm_nonneg (f₂ x), norm_nonneg (f₃ x)]

/-- If `‖f‖ ≤ c ‖g‖` almost everywhere with `f, g ∈ L²`, then `∫ ‖f‖² ≤ c² ∫ ‖g‖²`. -/
theorem integral_norm_sq_le_sq_mul_of_norm_le {α E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : α → F}
    {c : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hle : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf)
    (((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg).const_mul _) ?_
  filter_upwards [hle] with x hx
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- Applying continuous linear maps `B x` with `‖B x‖ ≤ c` almost everywhere to `f ∈ L²` gives
`x ↦ B x (f x) ∈ L²`, with `∫ ‖B x (f x)‖² ≤ c² ∫ ‖f‖²`. -/
theorem memLp_clm_apply_and_integral_norm_sq_le {α 𝕜 E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {B : α → E →L[𝕜] F} {f : α → E} {c : ℝ}
    (hB : AEStronglyMeasurable B μ) (hc : ∀ᵐ x ∂μ, ‖B x‖ ≤ c) (hf : MemLp f 2 μ) :
    MemLp (fun x ↦ B x (f x)) 2 μ ∧ ∫ x, ‖B x (f x)‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hle : ∀ᵐ x ∂μ, ‖B x (f x)‖ ≤ c * ‖f x‖ := by
    filter_upwards [hc] with x hx
    exact ((B x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hm : MemLp (fun x ↦ B x (f x)) 2 μ :=
    hf.of_le_mul ((isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := E) (F := F)).continuous
      |>.comp_aestronglyMeasurable (hB.prodMk hf.aestronglyMeasurable)) hle
  exact ⟨hm, integral_norm_sq_le_sq_mul_of_norm_le hm hf hle⟩

/-- **Convergence in `L²` gives an almost everywhere convergent subsequence.** If
`∫ ‖f n - g‖² → 0` for `f n, g ∈ L²`, then a subsequence of `f n` converges to `g` almost
everywhere. -/
theorem exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq {α E : Type*}
    [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : MemLp g 2 μ) (h : Tendsto (fun n ↦ ∫ t, ‖f n t - g t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ t ∂μ, Tendsto (fun k ↦ f (ns k) t) atTop (𝓝 (g t)) := by
  refine (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_).exists_seq_tendsto_ae
  simp_rw [fun n ↦ ((hf n).sub hg).eLpNorm_two_eq_ofReal_sqrt_integral, Pi.sub_apply]
  have := ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).tendsto 0).comp h
  rw [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero] at this
  exact this

end MeasureTheory
