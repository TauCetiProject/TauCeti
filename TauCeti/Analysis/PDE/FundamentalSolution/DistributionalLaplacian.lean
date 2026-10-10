/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Gradient
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The planar Newtonian kernel is a fundamental solution of `-Δ`

The logarithmic kernel `G(z) = -(2π)⁻¹ log ‖z‖` on the plane `ℂ` satisfies the distributional
identity `-Δ G = δ₀`: for every `C²` function `f : ℂ → ℝ` with compact support,

`∫ z, Δ f z * G z = -f 0`,

and, with the pole moved to `a`, `∫ z, Δ f z * G (z - a) = -f a`. This is the two-dimensional
counterpart of `TauCeti.integral_laplacian_mul_newtonianKernel` for `ℝⁿ`, `n ≥ 3`, and it is the
identity that makes the planar Newtonian potential `G ⋆ f` solve Poisson's equation.

The argument has the same two steps as in higher dimensions.

* **The weak gradient.** `G` and its derivative `-(2π)⁻¹ ‖z‖⁻² ⟪z, ·⟫` are locally integrable, and
  integration by parts against `G` holds across the pole: for a `C¹` function `g` with compact
  support, `∫ G ∂ᵥg = -∫ (∂ᵥG) g`. The kernel is replaced by the smooth regularizations
  `-(4π)⁻¹ (log (‖z‖² + t) - log (1 + t))`, which are dominated by `|G|` and converge to `G` as
  `t → 0⁺`, and dominated convergence passes to the limit. In particular `G` is weakly
  differentiable on every open set, with weak derivative its classical one.
* **The flux.** Summing over an orthonormal basis turns `∫ Δ f G` into
  `-∫ ∇G · ∇f = (2π)⁻¹ ∫ ‖z‖⁻² f' z z`, which the radial fundamental theorem of calculus
  `TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self` evaluates to `-f 0`.

## Main declarations

* `TauCeti.locallyIntegrable_planarNewtonianKernel`: `G` is locally integrable.
* `TauCeti.locallyIntegrable_fderiv_planarNewtonianKernel`: so is its derivative.
* `TauCeti.integral_planarNewtonianKernel_mul_fderiv_eq_neg_fderiv_mul`: integration by parts
  against `G`.
* `TauCeti.hasWeakFDerivOn_planarNewtonianKernel`: the classical derivative of `G` is its weak
  derivative.
* `TauCeti.integral_laplacian_mul_planarNewtonianKernel`: `-Δ G = δ₀`.
* `TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`: the same identity with the pole
  at `a`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1, Theorem 1 (the case `n = 2`).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.4.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology TopologicalSpace

open scoped RealInnerProductSpace

/-- The planar Newtonian kernel is locally integrable. -/
theorem locallyIntegrable_planarNewtonianKernel : LocallyIntegrable planarNewtonianKernel := by
  have h : planarNewtonianKernel = fun z : ℂ ↦ -(2 * Real.pi)⁻¹ * Real.log ‖z‖ :=
    funext planarNewtonianKernel_def
  rw [h]
  exact locallyIntegrable_log_norm.smul (-(2 * Real.pi)⁻¹)

/-- The Fréchet derivative of the planar Newtonian kernel is locally integrable: its norm is
`(2π ‖z‖)⁻¹`, an integrable singularity in two dimensions. -/
theorem locallyIntegrable_fderiv_planarNewtonianKernel :
    LocallyIntegrable (fderiv ℝ planarNewtonianKernel) := by
  refine locallyIntegrable_of_norm_le_rpow (μ := volume) (by simp) (C := (2 * Real.pi)⁻¹)
    (α := 1) (by simp) ?_ (measurable_fderiv ℝ _).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  rw [norm_fderiv_planarNewtonianKernel hz, Real.rpow_neg_one, mul_inv]

/-- The planar Newtonian kernel regularized at scale `t`:
`-(4π)⁻¹ (log (‖z‖² + t) - log (1 + t))`. Subtracting the constant `log (1 + t)` makes the
absolute value at most `|G|` for every `t ≥ 0`. -/
private def regKernel (t : ℝ) (z : ℂ) : ℝ :=
  -(4 * Real.pi)⁻¹ * (Real.log (‖z‖ ^ 2 + t) - Real.log (1 + t))

/-- The derivative of the regularized kernel in the direction `v`. -/
private def regKernelDeriv (v : ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * (‖z‖ ^ 2 + t)⁻¹ * ⟪z, v⟫

private lemma regKernel_zero : regKernel 0 = planarNewtonianKernel := by
  funext z
  rw [regKernel, planarNewtonianKernel_def, add_zero, add_zero, Real.log_one, sub_zero,
    Real.log_pow]
  ring

private lemma regKernelDeriv_zero (v : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regKernelDeriv v 0 z = fderiv ℝ planarNewtonianKernel z v := by
  rw [regKernelDeriv, fderiv_planarNewtonianKernel_apply hz, add_zero]

private lemma hasLineDerivAt_regKernel (v : ℂ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasLineDerivAt ℝ (regKernel t) (regKernelDeriv v t z) z v := by
  have hpos : 0 < ‖z‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const t).log hpos.ne').sub_const
    (Real.log (1 + t))).const_mul (-(4 * Real.pi)⁻¹)
  refine (h.hasLineDerivAt v).congr_deriv ?_
  simp only [regKernelDeriv, smul_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

private lemma continuous_regKernel {t : ℝ} (ht : 0 < t) : Continuous (regKernel t) :=
  continuous_const.mul ((((continuous_norm.pow 2).add continuous_const).log
    fun _ ↦ (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne').sub continuous_const)

private lemma continuous_regKernelDeriv (v : ℂ) {t : ℝ} (ht : 0 < t) :
    Continuous (regKernelDeriv v t) :=
  (continuous_const.mul (((continuous_norm.pow 2).add continuous_const).inv₀
    fun _ ↦ (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne')).mul
      (continuous_id.inner continuous_const)

/-- For `r > 0` and `t ≥ 0`, `|log (r + t) - log (1 + t)| ≤ |log r|`: the quotient
`(r + t) / (1 + t)` lies between `r` and `1`. -/
private lemma abs_log_add_sub_log_one_add_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    |Real.log (r + t) - Real.log (1 + t)| ≤ |Real.log r| := by
  have hrt : 0 < r + t := by linarith
  have h1t : 0 < 1 + t := by linarith
  have hmul : Real.log r + Real.log (1 + t) = Real.log (r * (1 + t)) :=
    (Real.log_mul hr.ne' h1t.ne').symm
  rcases le_total 1 r with h | h
  · have h₀ : Real.log (1 + t) ≤ Real.log (r + t) := Real.log_le_log h1t (by linarith)
    have h₁ : Real.log (r + t) ≤ Real.log (r * (1 + t)) := Real.log_le_log hrt (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (Real.log_nonneg h)]
    linarith
  · have h₀ : Real.log (r + t) ≤ Real.log (1 + t) := Real.log_le_log hrt (by linarith)
    have h₁ : Real.log (r * (1 + t)) ≤ Real.log (r + t) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (Real.log_nonpos hr.le h)]
    linarith

/-- The regularized kernels are dominated by the kernel away from the origin. -/
private lemma abs_regKernel_le {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ≠ 0) :
    |regKernel t z| ≤ |regKernel 0 z| := by
  have h := abs_log_add_sub_log_one_add_le (pow_pos (norm_pos_iff.mpr hz) 2) ht
  simp only [regKernel, abs_mul, add_zero, Real.log_one, sub_zero]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The derivatives of the regularized kernels are dominated by the regularization at `t = 0`,
which is the derivative of the kernel, away from the origin. -/
private lemma abs_regKernelDeriv_le (v : ℂ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ≠ 0) :
    |regKernelDeriv v t z| ≤ |regKernelDeriv v 0 z| := by
  have hpos : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
  simp only [regKernelDeriv, abs_mul, add_zero, abs_inv,
    abs_of_pos (add_pos_of_pos_of_nonneg hpos ht), abs_of_pos hpos]
  gcongr
  linarith

private lemma tendsto_regKernel {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun t ↦ regKernel t z) (𝓝[>] 0) (𝓝 (regKernel 0 z)) := by
  have hpos : (‖z‖ ^ 2 + 0 : ℝ) ≠ 0 := by simpa using hz
  exact ((((continuousAt_const.add continuousAt_id).log hpos).sub
    ((continuousAt_const.add continuousAt_id).log (by norm_num))).const_mul
      (-(4 * Real.pi)⁻¹)).tendsto.mono_left nhdsWithin_le_nhds

private lemma tendsto_regKernelDeriv (v : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun t ↦ regKernelDeriv v t z) (𝓝[>] 0) (𝓝 (regKernelDeriv v 0 z)) := by
  have hpos : (‖z‖ ^ 2 + 0 : ℝ) ≠ 0 := by simpa using hz
  exact (((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).inv₀ hpos)).mul
    continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds

/-- A compactly supported continuous function is integrable against the planar Newtonian
kernel. -/
private lemma integrable_planarNewtonianKernel_mul {w : ℂ → ℝ} (hw : Continuous w)
    (hc : HasCompactSupport w) : Integrable (fun z ↦ planarNewtonianKernel z * w z) :=
  locallyIntegrable_planarNewtonianKernel.integrable_smul_right_of_hasCompactSupport hw hc

/-- A compactly supported continuous function is integrable against a directional derivative of
the planar Newtonian kernel. -/
private lemma integrable_fderiv_planarNewtonianKernel_mul (v : ℂ) {w : ℂ → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun z ↦ fderiv ℝ planarNewtonianKernel z v * w z) := by
  simpa [mul_comm] using
    (locallyIntegrable_fderiv_planarNewtonianKernel.integrable_smul_left_of_hasCompactSupport hw
      hc).apply_continuousLinearMap v

/-- **Integration by parts against the planar Newtonian kernel.** For a `C¹` function `g` with
compact support on `ℂ`, `∫ G ∂ᵥg = -∫ (∂ᵥG) g`, although `G` is singular at the origin. -/
theorem integral_planarNewtonianKernel_mul_fderiv_eq_neg_fderiv_mul {g : ℂ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (v : ℂ) :
    ∫ z, planarNewtonianKernel z * fderiv ℝ g z v =
      -∫ z, fderiv ℝ planarNewtonianKernel z v * g z := by
  have hg' : Continuous fun z ↦ fderiv ℝ g z v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun z ↦ fderiv ℝ g z v :=
    (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L v) rfl
  -- Integration by parts for the smooth regularizations.
  have hibp : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ z, regKernel t z * fderiv ℝ g z v =
      -∫ z, regKernelDeriv v t z * g z := eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ by
    simpa using integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (f := regKernel t) (f' := regKernelDeriv v t)
      (g := g) (g' := fun z ↦ fderiv ℝ g z v)
      (((continuous_regKernelDeriv v ht).mul hg.continuous).integrable_of_hasCompactSupport
        hc.mul_left)
      (((continuous_regKernel ht).mul hg').integrable_of_hasCompactSupport hcg'.mul_left)
      (((continuous_regKernel ht).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun z _ ↦ hasLineDerivAt_regKernel v ht z)
      (fun z _ ↦ ((hg.differentiable one_ne_zero) z).hasFDerivAt.hasLineDerivAt v)
  -- At `t = 0` the regularizations are the kernel and, away from the pole, its derivative.
  have hderiv : (fun z ↦ fderiv ℝ planarNewtonianKernel z v * g z) =ᵐ[volume]
      fun z ↦ regKernelDeriv v 0 z * g z := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    rw [regKernelDeriv_zero v hz]
  -- Both sides converge as `t → 0⁺`.
  have hL := tendsto_integral_mul_of_dominated_away (0 : ℂ) (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (K := regKernel) (K₀ := regKernel 0) hg'
    (eventually_mem_nhdsWithin.mono fun t ht ↦ continuous_regKernel ht)
    (by simpa [regKernel_zero] using integrable_planarNewtonianKernel_mul hg' hcg')
    (eventually_mem_nhdsWithin.mono fun t ht z hz ↦ abs_regKernel_le (le_of_lt ht) hz)
    (fun z hz ↦ tendsto_regKernel hz)
  have hR := tendsto_integral_mul_of_dominated_away (0 : ℂ) (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (K := regKernelDeriv v) (K₀ := regKernelDeriv v 0) hg.continuous
    (eventually_mem_nhdsWithin.mono fun t ht ↦ continuous_regKernelDeriv v ht)
    ((integrable_fderiv_planarNewtonianKernel_mul v hg.continuous hc).congr hderiv)
    (eventually_mem_nhdsWithin.mono fun t ht z hz ↦ abs_regKernelDeriv_le v (le_of_lt ht) hz)
    (fun z hz ↦ tendsto_regKernelDeriv v hz)
  rw [regKernel_zero] at hL
  rw [integral_congr_ae hderiv]
  exact tendsto_nhds_unique (hL.congr' hibp) hR.neg

/-- **The planar Newtonian kernel is weakly differentiable.** On every open subset of `ℂ`, the
classical derivative of `G`, which exists away from the origin, is a weak derivative of `G`. -/
theorem hasWeakFDerivOn_planarNewtonianKernel (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω planarNewtonianKernel (fderiv ℝ planarNewtonianKernel) :=
  hasWeakFDerivOn_of_forall_integral_fderiv_smul locallyIntegrable_planarNewtonianKernel
    locallyIntegrable_fderiv_planarNewtonianKernel (fun _ hg hc v ↦ by
      simpa only [smul_eq_mul, mul_comm] using
        integral_planarNewtonianKernel_mul_fderiv_eq_neg_fderiv_mul hg hc v) Ω

/-- Away from the pole, the gradient pairing `∇G · ∇f` is `-(2π)⁻¹ ‖z‖⁻² f' z z`. -/
private lemma sum_fderiv_planarNewtonianKernel_mul_fderiv (b : OrthonormalBasis (Fin 2) ℝ ℂ)
    (f : ℂ → ℝ) {z : ℂ} (hz : z ≠ 0) :
    ∑ i, fderiv ℝ planarNewtonianKernel z (b i) * fderiv ℝ f z (b i) =
      -(2 * Real.pi)⁻¹ * (‖z‖ ^ (-(2 : ℝ)) * fderiv ℝ f z z) := by
  have hz' : fderiv ℝ f z z = ∑ i, ⟪b i, z⟫ * fderiv ℝ f z (b i) := by
    have h := congrArg (fderiv ℝ f z) (b.sum_repr' z).symm
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  simp_rw [fderiv_planarNewtonianKernel_apply hz, hz', Finset.mul_sum, real_inner_comm z,
    Real.rpow_neg (norm_nonneg z), Real.rpow_two]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The planar Newtonian kernel is a fundamental solution of `-Δ`.** For every `C²` function
`f` with compact support on `ℂ`, `∫ Δ f · G = -f 0`; that is, `-Δ G = δ₀` in the sense of
distributions. -/
theorem integral_laplacian_mul_planarNewtonianKernel {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∫ z, Δ f z * planarNewtonianKernel z = -f 0 := by
  have hrad := integral_norm_rpow_neg_finrank_mul_fderiv_apply_self
    (μ := (volume : Measure ℂ)) (hf.of_le (by norm_num)) hc
  rw [Complex.finrank_real_complex] at hrad
  have hvol : volume.real (ball (0 : ℂ) 1) = Real.pi := by simp [Measure.real]
  rw [hvol] at hrad
  set b := Complex.orthonormalBasisOneI
  have hsum : (fun z ↦ ∑ i, fderiv ℝ planarNewtonianKernel z (b i) * fderiv ℝ f z (b i))
      =ᵐ[volume] fun z ↦ -(2 * Real.pi)⁻¹ * (‖z‖ ^ (-(2 : ℝ)) * fderiv ℝ f z z) := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact sum_fderiv_planarNewtonianKernel_mul_fderiv b f hz
  rw [integral_laplacian_mul_eq_neg_integral_sum locallyIntegrable_planarNewtonianKernel
      locallyIntegrable_fderiv_planarNewtonianKernel
      (fun _ ↦ integral_planarNewtonianKernel_mul_fderiv_eq_neg_fderiv_mul) hf hc b,
    integral_congr_ae hsum, integral_const_mul]
  push_cast at hrad
  rw [hrad]
  field_simp

/-- **The planar Newtonian kernel with pole `a` is a fundamental solution of `-Δ`.** For every
`C²` function `f` with compact support on `ℂ`, `∫ Δ f · G(· - a) = -f a`. -/
theorem integral_laplacian_mul_planarNewtonianKernel_sub {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (a : ℂ) :
    ∫ z, Δ f z * planarNewtonianKernel (z - a) = -f a := by
  have h := integral_laplacian_mul_planarNewtonianKernel (f := fun y ↦ f (y + a))
    (hf.comp (contDiff_id.add contDiff_const)) (hc.comp_homeomorph (Homeomorph.addRight a))
  rw [laplacian_comp_add_right, zero_add] at h
  rw [← h, ← integral_add_right_eq_self _ a]
  simp

end TauCeti
