/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.PDE.FundamentalSolution.DistributionalLaplacian

/-!
# The planar Newtonian potential solves Poisson's equation

For `f : ℂ → F` with compact support, the **Newtonian potential** of `f` in the plane is the
convolution `u = G ⋆ f`, `u z = ∫ G(z - w) f(w) dw`, of `f` with the logarithmic kernel
`G = TauCeti.planarNewtonianKernel`, `G z = -(2π)⁻¹ log ‖z‖`. For `f` of class `C²` with compact
support:

* `u` is as smooth as `f`;
* `u` solves **Poisson's equation** `-Δu = f` on all of `ℂ`;
* `u` is harmonic off the support of `f`;
* `u` grows like `G` times the total mass of `f`: `u z - G z • ∫ f → 0` as `z → ∞` (already for
  continuous `f` with compact support);
* `u` is the **unique** `C²` solution `v` of `-Δv = f` with `v z - G z • ∫ f → 0` at infinity.

Unlike in dimension `n ≥ 3` (`TauCeti.laplacian_newtonianKernel_convolution`), the potential does
not tend to zero at infinity unless `∫ f = 0`; the logarithmic term `G z • ∫ f` is the correct
normalization at infinity. Poisson's equation follows from the distributional identity
`-ΔG = δ` (`TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`) by
`TauCeti.laplacian_convolution_eq_neg_of_integral_laplacian_mul`, which moves the Laplacian onto
`f` under the convolution. Uniqueness
holds because a harmonic function on `ℂ` that vanishes at infinity is zero
(`InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`).

## Main declarations

* `TauCeti.contDiff_planarNewtonianKernel_convolution`: `G ⋆ f` is `C^k` when `f` is `C^k` with
  compact support.
* `TauCeti.laplacian_planarNewtonianKernel_convolution`: `Δ (G ⋆ f) = -f`.
* `TauCeti.harmonicOnNhd_planarNewtonianKernel_convolution`: `G ⋆ f` is harmonic off
  `tsupport f`.
* `TauCeti.tendsto_planarNewtonianKernel_convolution_sub_cocompact`:
  `(G ⋆ f) z - G z • ∫ f → 0` at infinity.
* `TauCeti.eq_planarNewtonianKernel_convolution_of_laplacian_eq_neg`: uniqueness among solutions
  with this behaviour at infinity.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1, Theorem 1 (the case `n = 2`).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.4 and Section 4.2.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}

/-- The planar Newtonian potential `G ⋆ f` of a `C^k` function `f` with compact support is
`C^k`. -/
theorem contDiff_planarNewtonianKernel_convolution {k : ℕ∞} (hf : ContDiff ℝ k f)
    (hc : HasCompactSupport f) : ContDiff ℝ k (planarNewtonianKernel ⋆ f) :=
  hc.contDiff_convolution_right _ locallyIntegrable_planarNewtonianKernel hf

/-- **The planar Newtonian potential solves Poisson's equation.** For `f` of class `C²` with
compact support on `ℂ`, the Newtonian potential `u = G ⋆ f` satisfies `-Δu = f`. -/
theorem laplacian_planarNewtonianKernel_convolution [CompleteSpace F] (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : Δ (planarNewtonianKernel ⋆ f) = -f :=
  laplacian_convolution_eq_neg_of_integral_laplacian_mul locallyIntegrable_planarNewtonianKernel
    (fun _ hφ hφc x ↦ by
      simp_rw [planarNewtonianKernel_sub_comm x]
      exact integral_laplacian_mul_planarNewtonianKernel_sub hφ hφc x) hf hc

/-- The planar Newtonian potential of a `C²` function `f` with compact support is harmonic off
the support of `f`. -/
theorem harmonicOnNhd_planarNewtonianKernel_convolution [CompleteSpace F] (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    HarmonicOnNhd (planarNewtonianKernel ⋆ f) (tsupport f)ᶜ := fun x hx => by
  refine ⟨(contDiff_planarNewtonianKernel_convolution hf hc).contDiffAt, ?_⟩
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [laplacian_planarNewtonianKernel_convolution hf hc, Pi.neg_apply,
    image_eq_zero_of_notMem_tsupport hy, neg_zero, Pi.zero_apply]

/-- Moving the pole of the planar Newtonian kernel by at most `R` changes its value at a point `z`
with `2 R ≤ ‖z‖` by at most `π⁻¹ R / ‖z‖`. -/
private lemma abs_planarNewtonianKernel_sub_sub_le {z y : ℂ} {R : ℝ} (hy : ‖y‖ ≤ R)
    (hz : 2 * R ≤ ‖z‖) (hz₀ : 0 < ‖z‖) :
    |planarNewtonianKernel (z - y) - planarNewtonianKernel z| ≤ Real.pi⁻¹ * (R / ‖z‖) := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  have hzy : ‖z‖ - R ≤ ‖z - y‖ := by linarith [norm_sub_norm_le z y]
  have hzy' : ‖z - y‖ ≤ ‖z‖ + R := by linarith [norm_sub_le z y]
  have hhalf : ‖z‖ / 2 ≤ ‖z - y‖ := by linarith
  have hpos : 0 < ‖z - y‖ := by linarith
  -- `|log a - log b| ≤ |a - b| / min a b`, here with `|a - b| ≤ R` and `min a b ≥ ‖z‖ / 2`.
  have hlog : |Real.log ‖z - y‖ - Real.log ‖z‖| ≤ 2 * (R / ‖z‖) := by
    have h₁ : Real.log ‖z - y‖ - Real.log ‖z‖ ≤ R / ‖z‖ := by
      rw [← Real.log_div hpos.ne' hz₀.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hpos hz₀)).trans ?_
      rw [div_sub_one hz₀.ne']
      exact div_le_div_of_nonneg_right (by linarith) hz₀.le
    have h₂ : Real.log ‖z‖ - Real.log ‖z - y‖ ≤ 2 * (R / ‖z‖) := by
      rw [← Real.log_div hz₀.ne' hpos.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hz₀ hpos)).trans ?_
      rw [div_sub_one hpos.ne']
      calc (‖z‖ - ‖z - y‖) / ‖z - y‖ ≤ R / (‖z‖ / 2) :=
            div_le_div₀ hR (by linarith) (by positivity) hhalf
        _ = 2 * (R / ‖z‖) := by field_simp
    have : 0 ≤ R / ‖z‖ := div_nonneg hR hz₀.le
    rw [abs_le]
    constructor <;> linarith
  rw [planarNewtonianKernel_def, planarNewtonianKernel_def, ← mul_sub, abs_mul, abs_neg,
    abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc (2 * Real.pi)⁻¹ * |Real.log ‖z - y‖ - Real.log ‖z‖|
      ≤ (2 * Real.pi)⁻¹ * (2 * (R / ‖z‖)) := by gcongr
    _ = Real.pi⁻¹ * (R / ‖z‖) := by field_simp

/-- **The planar Newtonian potential grows logarithmically.** For `f` continuous with compact
support on `ℂ`, `(G ⋆ f) z - G z • ∫ f → 0` as `z → ∞`: far from the support of `f`, the
potential is that of a point mass `∫ f` at the origin. -/
theorem tendsto_planarNewtonianKernel_convolution_sub_cocompact (hf : Continuous f)
    (hc : HasCompactSupport f) :
    Tendsto (fun z ↦ (planarNewtonianKernel ⋆ f) z - planarNewtonianKernel z • ∫ w, f w)
      (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hc
  -- The pointwise bound off a large ball.
  have hbound : ∀ z : ℂ, 2 * R' ≤ ‖z‖ →
      ‖(planarNewtonianKernel ⋆ f) z - planarNewtonianKernel z • ∫ w, f w‖ ≤
        Real.pi⁻¹ * (R' / ‖z‖) * ∫ w, ‖f w‖ := by
    intro z hz
    have hz₀ : 0 < ‖z‖ := by linarith
    have hconv : Integrable fun w ↦ planarNewtonianKernel (z - w) • f w := by
      have h := (hc.convolutionExists_right (lsmul ℝ ℝ) locallyIntegrable_planarNewtonianKernel
        hf z).integrable_swap
      simpa using h
    rw [convolution_lsmul_swap, ← integral_smul, ← integral_sub hconv
      (hfi.smul (planarNewtonianKernel z) : Integrable fun w ↦ planarNewtonianKernel z • f w),
      ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hfi.norm.const_mul _) (ae_of_all _ fun w => ?_)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    by_cases hw : w ∈ tsupport f
    · have hwR : ‖w‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hw)).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right (abs_planarNewtonianKernel_sub_sub_le hwR hz hz₀)
        (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hw]
  have hlim : Tendsto (fun z : ℂ ↦ Real.pi⁻¹ * (R' / ‖z‖) * ∫ w, ‖f w‖) (cocompact ℂ)
      (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul R'
    simpa [Function.comp_def, div_eq_mul_inv] using
      (h.const_mul Real.pi⁻¹).mul_const (∫ w, ‖f w‖)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (2 * R')] with z hz
  exact hbound z hz

/-- **Uniqueness for Poisson's equation in the plane.** For `f` of class `C²` with compact
support on `ℂ`, the Newtonian potential `G ⋆ f` is the only `C²` solution `v` of `-Δv = f` with
`v z - G z • ∫ f → 0` at infinity. -/
theorem eq_planarNewtonianKernel_convolution_of_laplacian_eq_neg [CompleteSpace F]
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {v : ℂ → F} (hv : ContDiff ℝ 2 v)
    (hΔ : Δ v = -f)
    (hv₀ : Tendsto (fun z ↦ v z - planarNewtonianKernel z • ∫ w, f w) (cocompact ℂ) (𝓝 0)) :
    v = planarNewtonianKernel ⋆ f := by
  have hu := contDiff_planarNewtonianKernel_convolution hf hc
  have hw : HarmonicOnNhd (v - planarNewtonianKernel ⋆ f) univ := fun x _ =>
    ⟨(hv.sub hu).contDiffAt, Eventually.of_forall fun y => by
      rw [hv.contDiffAt.laplacian_sub hu.contDiffAt, hΔ,
        laplacian_planarNewtonianKernel_convolution hf hc, sub_self, Pi.zero_apply]⟩
  have hw₀ := hv₀.sub (tendsto_planarNewtonianKernel_convolution_sub_cocompact hf.continuous hc)
  rw [sub_zero] at hw₀
  refine sub_eq_zero.1 (hw.eq_zero_of_tendsto_cocompact ?_)
  refine hw₀.congr fun z => ?_
  simp

end TauCeti
