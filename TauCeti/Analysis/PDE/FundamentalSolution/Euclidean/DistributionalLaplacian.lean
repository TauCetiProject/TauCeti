/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Regularization
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The Newtonian kernel is a fundamental solution of `-Δ`

For `n ≥ 3`, the Newtonian kernel `Gₙ(x) = (n (n - 2) ωₙ)⁻¹ ‖x‖²⁻ⁿ` on `ℝⁿ` satisfies the
distributional identity `-Δ Gₙ = δ₀`: for every `C²` function `f` with compact support,

`∫ x, Δ f x * Gₙ x = -f 0`,

and, with the pole moved to `a`, `∫ x, Δ f x * Gₙ (x - a) = -f a`.

The proof has two steps.

* **The weak gradient.** Integration by parts against `Gₙ` holds across the pole: for a `C¹`
  function `g` with compact support, `∫ Gₙ ∂ᵥg = -∫ (∂ᵥGₙ) g`.  The kernel is replaced by the
  smooth regularizations `C (‖x‖² + t) ^ ((2 - n) / 2)`, for which Mathlib's integration by parts
  applies, and `t → 0⁺` by dominated convergence: both the regularized kernels and their
  derivatives are dominated by the kernel and its derivative.  In particular `Gₙ` is weakly
  differentiable on every open set with weak derivative its classical one.
* **The flux.** Summing over an orthonormal basis turns `∫ Δ f Gₙ` into
  `-∫ ∇Gₙ · ∇f = (n ωₙ)⁻¹ ∫ ‖x‖⁻ⁿ f' x x`, and the radial fundamental theorem of calculus
  `TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self` evaluates the latter integral as
  `-(n ωₙ) f 0`.

The statement and the normalization follow Evans, *Partial Differential Equations*, Section 2.2.1,
Theorem 1, whose Green's-identity argument on the complement of a small ball is replaced here by
the two steps above.

## Main declarations

* `TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`: integration by parts against
  the Newtonian kernel.
* `TauCeti.hasWeakFDerivOn_newtonianKernel`: the classical derivative of the kernel is its weak
  derivative.
* `TauCeti.integral_laplacian_mul_newtonianKernel`: `-Δ Gₙ = δ₀`.
* `TauCeti.integral_laplacian_mul_newtonianKernel_sub`: the same identity with the pole at `a`.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology TopologicalSpace

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The normalizing constant `(n (n - 2) ωₙ)⁻¹` of the Newtonian kernel. -/
private abbrev kernelConst (n : ℕ) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹

/-- The Newtonian kernel regularized at scale `t`: `C (‖x‖² + t) ^ ((2 - n) / 2)`. -/
private def regKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  kernelConst n * (‖x‖ ^ 2 + t) ^ ((2 - (n : ℝ)) / 2)

/-- The derivative of the regularized kernel in the direction `v`. -/
private def regKernelDeriv (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  kernelConst n * (2 - (n : ℝ)) * (‖x‖ ^ 2 + t) ^ ((2 - (n : ℝ)) / 2 - 1) * ⟪x, v⟫

private lemma regKernel_zero (n : ℕ) : regKernel n 0 = newtonianKernel n := by
  funext x
  rw [regKernel, newtonianKernel_def, add_zero, sq_rpow_div_two (norm_nonneg x)]

private lemma regKernelDeriv_zero (hn : 3 ≤ n) (v : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    regKernelDeriv n v 0 x = fderiv ℝ (newtonianKernel n) x v := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hvol := (volume_real_unitBall_pos n).ne'
  rw [regKernelDeriv, fderiv_newtonianKernel_apply n (by omega) hx, add_zero,
    show (2 - (n : ℝ)) / 2 - 1 = -(n : ℝ) / 2 by ring, sq_rpow_div_two (norm_nonneg x)]
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (n : ℝ) ≠ 0 := by linarith
  field_simp
  ring

private lemma hasLineDerivAt_regKernel (v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasLineDerivAt ℝ (regKernel n t) (regKernelDeriv n v t x) x v := by
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const
    (p := (2 - (n : ℝ)) / 2) (Or.inl hpos.ne')).const_mul (kernelConst n)
  refine (h.hasLineDerivAt v).congr_deriv ?_
  simp only [regKernelDeriv, smul_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

private lemma continuous_regKernel {t : ℝ} (ht : 0 < t) : Continuous (regKernel n t) :=
  continuous_const.mul (((continuous_norm.pow 2).add continuous_const).rpow_const
    fun _ ↦ Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne')

private lemma continuous_regKernelDeriv (v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    Continuous (regKernelDeriv n v t) :=
  (continuous_const.mul (((continuous_norm.pow 2).add continuous_const).rpow_const
    fun _ ↦ Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne')).mul
      (continuous_id.inner continuous_const)

/-- The regularized kernels are dominated by the kernel away from the origin. -/
private lemma abs_regKernel_le (hn : 3 ≤ n) {t : ℝ} (ht : 0 ≤ t) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : |regKernel n t x| ≤ |regKernel n 0 x| := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hconst : 0 ≤ kernelConst n :=
    inv_nonneg.mpr (mul_nonneg (by nlinarith) (volume_real_unitBall_pos n).le)
  simp only [regKernel, abs_mul, abs_of_nonneg hconst,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) le_rfl) _)]
  exact mul_le_mul_of_nonneg_left (sq_add_rpow_le (norm_ne_zero_iff.mpr hx) ht (by linarith))
    hconst

/-- The derivatives of the regularized kernels are dominated by the regularization at `t = 0`,
which is the derivative of the kernel, away from the origin. -/
private lemma abs_regKernelDeriv_le (hn : 3 ≤ n) (v : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 ≤ t) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    |regKernelDeriv n v t x| ≤ |regKernelDeriv n v 0 x| := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [regKernelDeriv, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) le_rfl) _)]
  gcongr ?_ * _
  exact mul_le_mul_of_nonneg_left (sq_add_rpow_le (norm_ne_zero_iff.mpr hx) ht (by linarith))
    (by positivity)

/-- A compactly supported continuous function is integrable against the Newtonian kernel. -/
private lemma integrable_newtonianKernel_mul {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun x ↦ newtonianKernel n x * w x) :=
  (locallyIntegrable_newtonianKernel n).integrable_smul_right_of_hasCompactSupport hw hc

/-- A compactly supported continuous function is integrable against a directional derivative of
the Newtonian kernel. -/
private lemma integrable_fderiv_newtonianKernel_mul (v : EuclideanSpace ℝ (Fin n))
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun x ↦ fderiv ℝ (newtonianKernel n) x v * w x) := by
  simpa [mul_comm] using
    ((locallyIntegrable_fderiv_newtonianKernel n).integrable_smul_left_of_hasCompactSupport hw
      hc).apply_continuousLinearMap v

/-- **Integration by parts against the Newtonian kernel.** For `n ≥ 3` and a `C¹` function `g`
with compact support, `∫ Gₙ ∂ᵥg = -∫ (∂ᵥGₙ) g`, although `Gₙ` is singular at the origin. -/
theorem integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul (hn : 3 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, newtonianKernel n x * fderiv ℝ g x v =
      -∫ x, fderiv ℝ (newtonianKernel n) x v * g x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hg' : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun x ↦ fderiv ℝ g x v :=
    (hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L v) rfl
  -- Integration by parts for the smooth regularizations.
  have hibp : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ x, regKernel n t x * fderiv ℝ g x v =
      -∫ x, regKernelDeriv n v t x * g x := eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ by
    simpa using integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (f := regKernel n t) (f' := regKernelDeriv n v t)
      (g := g) (g' := fun x ↦ fderiv ℝ g x v)
      (((continuous_regKernelDeriv v ht).mul hg.continuous).integrable_of_hasCompactSupport
        hc.mul_left)
      (((continuous_regKernel ht).mul hg').integrable_of_hasCompactSupport hcg'.mul_left)
      (((continuous_regKernel ht).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ ↦ hasLineDerivAt_regKernel v ht x)
      (fun x _ ↦ ((hg.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
  -- At `t = 0` the regularizations are the kernel and, away from the pole, its derivative.
  have hderiv : (fun x ↦ fderiv ℝ (newtonianKernel n) x v * g x) =ᵐ[volume]
      fun x ↦ regKernelDeriv n v 0 x * g x := by
    filter_upwards [volume.ae_ne 0] with x hx
    rw [regKernelDeriv_zero hn v hx]
  -- Both sides converge as `t → 0⁺`.
  have hL := tendsto_integral_mul_of_dominated_away (0 : EuclideanSpace ℝ (Fin n))
    (l := 𝓝[>] (0 : ℝ)) (K := regKernel n) (K₀ := regKernel n 0) hg'
    (eventually_mem_nhdsWithin.mono fun t ht ↦ continuous_regKernel ht)
    (by simpa [regKernel_zero] using integrable_newtonianKernel_mul hg' hcg')
    (eventually_mem_nhdsWithin.mono fun t ht x hx ↦ abs_regKernel_le hn (le_of_lt ht) hx)
    (fun x hx ↦ (tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _).const_mul _)
  have hR := tendsto_integral_mul_of_dominated_away (0 : EuclideanSpace ℝ (Fin n))
    (l := 𝓝[>] (0 : ℝ)) (K := regKernelDeriv n v) (K₀ := regKernelDeriv n v 0) hg.continuous
    (eventually_mem_nhdsWithin.mono fun t ht ↦ continuous_regKernelDeriv v ht)
    ((integrable_fderiv_newtonianKernel_mul v hg.continuous hc).congr hderiv)
    (eventually_mem_nhdsWithin.mono fun t ht x hx ↦
      abs_regKernelDeriv_le hn v (le_of_lt ht) hx)
    (fun x hx ↦ ((tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _).const_mul _).mul_const _)
  rw [regKernel_zero] at hL
  rw [integral_congr_ae hderiv]
  exact tendsto_nhds_unique (hL.congr' hibp) hR.neg

/-- **The Newtonian kernel is weakly differentiable.** For `n ≥ 3`, on every open set the
classical derivative of `Gₙ`, which exists away from the origin, is a weak derivative of `Gₙ`. -/
theorem hasWeakFDerivOn_newtonianKernel (hn : 3 ≤ n) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    HasWeakFDerivOn volume Ω (newtonianKernel n) (fderiv ℝ (newtonianKernel n)) := by
  refine hasWeakFDerivOn_iff.mpr fun v ↦ hasWeakLineDerivOn_iff_testFunction.mpr ⟨inferInstance,
    (locallyIntegrable_newtonianKernel n).locallyIntegrableOn _, ?_, fun φ ↦ ?_⟩
  · simpa [Function.comp_def] using (ContinuousLinearMap.apply ℝ ℝ v).locallyIntegrableOn_comp
      ((locallyIntegrable_fderiv_newtonianKernel n).locallyIntegrableOn Ω)
  have hφ : ContDiff ℝ 1 (φ : EuclideanSpace ℝ (Fin n) → ℝ) := φ.contDiff.of_le (by simp)
  have h := integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul hn hφ φ.hasCompactSupport v
  simp_rw [((hφ.differentiable one_ne_zero) _).lineDeriv_eq_fderiv, smul_eq_mul]
  simpa only [mul_comm] using h

/-- Integration by parts in each coordinate direction turns `∫ Δ f · Gₙ` into the negative of
the integrated gradient pairing `∇Gₙ · ∇f`. -/
private lemma integral_laplacian_mul_newtonianKernel_eq_neg_integral_sum (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∫ x, Δ f x * newtonianKernel n x =
      -∫ x, ∑ i, fderiv ℝ (newtonianKernel n) x (b i) * fderiv ℝ f x (b i) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi : ∀ i, ContDiff ℝ 1 fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    hf1.clm_apply contDiff_const
  have hci : ∀ i, HasCompactSupport fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    (hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L (b i)) rfl
  -- The Laplacian as a sum of iterated directional derivatives.
  have hΔ : ∀ x, Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) := fun x ↦ by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply
      ((hf1.differentiable one_ne_zero) x) (differentiableAt_const _)]
    simp
  simp_rw [hΔ, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ ?_, integral_finsetSum _ fun i _ ↦
    integrable_fderiv_newtonianKernel_mul _ (hgi i).continuous (hci i), ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul hn (hgi i) (hci i) (b i)]
    simp_rw [mul_comm]
  · simpa [mul_comm] using integrable_newtonianKernel_mul
      (((hgi i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (((hci i).fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L (b i)) rfl)

/-- Away from the pole, the gradient pairing `∇Gₙ · ∇f` is `-(n ωₙ)⁻¹ ‖x‖⁻ⁿ f' x x`. -/
private lemma sum_fderiv_newtonianKernel_mul_fderiv (hn : 3 ≤ n)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ i, fderiv ℝ (newtonianKernel n) x (b i) * fderiv ℝ f x (b i) =
      -((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ (-(n : ℝ)) * fderiv ℝ f x x) := by
  have hx' : fderiv ℝ f x x = ∑ i, ⟪b i, x⟫ * fderiv ℝ f x (b i) := by
    simpa using congrArg (fderiv ℝ f x) (b.sum_repr' x).symm
  simp_rw [fderiv_newtonianKernel_apply n (by omega) hx, hx', Finset.mul_sum, real_inner_comm x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The Newtonian kernel is a fundamental solution of `-Δ`.** For `n ≥ 3` and every `C²`
function `f` with compact support on `ℝⁿ`, `∫ Δ f · Gₙ = -f 0`; that is, `-Δ Gₙ = δ₀` in the
sense of distributions. -/
theorem integral_laplacian_mul_newtonianKernel (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ x, Δ f x * newtonianKernel n x = -f 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hvol := (volume_real_unitBall_pos n).ne'
  have hrad := integral_norm_rpow_neg_finrank_mul_fderiv_apply_self
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hf.of_le (by norm_num)) hc
  rw [finrank_euclideanSpace_fin] at hrad
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum : (fun x ↦ ∑ i, fderiv ℝ (newtonianKernel n) x (b i) * fderiv ℝ f x (b i)) =ᵐ[volume]
      fun x ↦ -((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ (-(n : ℝ)) * fderiv ℝ f x x) := by
    filter_upwards [volume.ae_ne 0] with x hx
    exact sum_fderiv_newtonianKernel_mul_fderiv hn b f hx
  rw [integral_laplacian_mul_newtonianKernel_eq_neg_integral_sum hn hf hc b,
    integral_congr_ae hsum, integral_const_mul, hrad]
  have h0 : (n : ℝ) ≠ 0 := by linarith
  field_simp

/-- **The Newtonian kernel with pole `a` is a fundamental solution of `-Δ`.** For `n ≥ 3` and
every `C²` function `f` with compact support on `ℝⁿ`, `∫ Δ f · Gₙ(· - a) = -f a`. -/
theorem integral_laplacian_mul_newtonianKernel_sub (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, Δ f x * newtonianKernel n (x - a) = -f a := by
  have h := integral_laplacian_mul_newtonianKernel hn (f := fun y ↦ f (y + a))
    (hf.comp (contDiff_id.add contDiff_const)) (hc.comp_homeomorph (Homeomorph.addRight a))
  rw [laplacian_comp_add_right, zero_add] at h
  rw [← h, ← integral_add_right_eq_self _ a]
  simp

end TauCeti
