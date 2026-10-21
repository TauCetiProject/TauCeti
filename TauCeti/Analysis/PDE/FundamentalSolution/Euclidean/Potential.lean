/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Hessian

/-!
# The Newtonian potential solves Poisson's equation

For `f : ℝⁿ → F` with compact support, the **Newtonian potential** of `f` is the convolution
`u = Gₙ ⋆ f`, `u x = ∫ Gₙ(x - y) f(y) dy`, of `f` with the Newtonian kernel
`Gₙ = TauCeti.newtonianKernel n`. For `n ≥ 3` and `f` of class `C²` with compact support:

* `u` is as smooth as `f` (no restriction on `n` is needed here);
* `u` solves **Poisson's equation** `-Δu = f` on all of `ℝⁿ`;
* `u` is harmonic off the support of `f`, where its second derivatives are obtained by
  integrating `f` against the Hessian of `Gₙ` (for this, too, any `n`);
* `u` decays like `‖x‖ ^ (2 - n)` (this does need `n ≥ 3`, but already holds for integrable `f`
  with bounded support), and so tends to zero at infinity;
* `u` is the **unique** `C²` solution of `-Δv = f` that tends to zero at infinity.

The Laplacian falls on `f` under the convolution (`HasCompactSupport.laplacian_convolution_right`),
and the distributional identity `-ΔGₙ = δ` (`TauCeti.integral_laplacian_mul_newtonianKernel_sub`)
evaluates the result. Off the support of `f`, two integrations by parts move the derivatives
from `f` onto the kernel, which is smooth there. Uniqueness holds because a harmonic function on
`ℝⁿ` that vanishes at infinity is zero
(`InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`).

## Main declarations

* `TauCeti.contDiff_newtonianKernel_convolution`: `Gₙ ⋆ f` is `C^k` when `f` is `C^k` with
  compact support.
* `TauCeti.laplacian_newtonianKernel_convolution`: `Δ (Gₙ ⋆ f) = -f`.
* `TauCeti.harmonicOnNhd_newtonianKernel_convolution`: `Gₙ ⋆ f` is harmonic off `tsupport f`.
* `TauCeti.norm_newtonianKernel_convolution_le`: for `n ≥ 3`, the decay bound
  `‖(Gₙ ⋆ f) x‖ ≤ C (‖x‖ - R) ^ (2 - n) ∫ ‖f‖` off the ball `closedBall 0 R` containing the
  support of `f`, and the companion bound `TauCeti.norm_fderiv_newtonianKernel_convolution_le`,
  `‖D(Gₙ ⋆ f) x‖ ≤ C' (‖x‖ - R) ^ (1 - n) ∫ ‖f‖` for `n ≠ 2`, on its derivative.
* `TauCeti.tendsto_newtonianKernel_convolution_cocompact`: for `n ≥ 3`, `Gₙ ⋆ f → 0` at
  infinity.
* `TauCeti.eq_newtonianKernel_convolution_of_laplacian_eq_neg`: uniqueness among solutions
  vanishing at infinity.
* `TauCeti.iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport`: off the
  support of `f`, `D²(Gₙ ⋆ f)(x)(v, w) = ∫ D²Gₙ(x - y)(v, w) f(y) dy`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1, Theorem 1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.5 and Section 4.2.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology
open scoped Convolution

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : EuclideanSpace ℝ (Fin n) → F}

/-- The Newtonian potential `Gₙ ⋆ f` of a `C^k` function `f` with compact support is `C^k`. -/
theorem contDiff_newtonianKernel_convolution {k : ℕ∞} (hf : ContDiff ℝ k f)
    (hc : HasCompactSupport f) : ContDiff ℝ k (newtonianKernel n ⋆ f) :=
  hc.contDiff_convolution_right _ (locallyIntegrable_newtonianKernel n) hf

/-- **The Newtonian potential solves Poisson's equation.** For `n ≥ 3` and `f` of class `C²`
with compact support on `ℝⁿ`, the Newtonian potential `u = Gₙ ⋆ f` satisfies `-Δu = f`. -/
theorem laplacian_newtonianKernel_convolution [CompleteSpace F] (hn : 3 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : Δ (newtonianKernel n ⋆ f) = -f :=
  laplacian_convolution_eq_neg_of_integral_laplacian_mul (locallyIntegrable_newtonianKernel n)
    (fun _ hφ hφc x ↦ by
      simp_rw [newtonianKernel_sub_comm n x]
      exact integral_laplacian_mul_newtonianKernel_sub hn hφ hφc x) hf hc

/-- For `n ≥ 3`, the Newtonian potential of a `C²` function `f` with compact support is harmonic
off the support of `f`. -/
theorem harmonicOnNhd_newtonianKernel_convolution [CompleteSpace F] (hn : 3 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    HarmonicOnNhd (newtonianKernel n ⋆ f) (tsupport f)ᶜ := fun x hx => by
  refine ⟨(contDiff_newtonianKernel_convolution hf hc).contDiffAt, ?_⟩
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [laplacian_newtonianKernel_convolution hn hf hc, Pi.neg_apply,
    image_eq_zero_of_notMem_tsupport hy, neg_zero, Pi.zero_apply]

/-- **Decay of the Newtonian potential.** For `n ≥ 3` and `f` integrable on `ℝⁿ` and vanishing
off `closedBall 0 R`, at every point `x` with `R < ‖x‖`,

`‖(Gₙ ⋆ f) x‖ ≤ (n (n - 2) ωₙ)⁻¹ (‖x‖ - R) ^ (2 - n) ∫ ‖f‖`,

where `ωₙ` is the volume of the unit ball. -/
theorem norm_newtonianKernel_convolution_le (hn : 3 ≤ n) (hf : Integrable f) {R : ℝ}
    (hR : Function.support f ⊆ closedBall 0 R) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) :
    ‖(newtonianKernel n ⋆ f) x‖ ≤
      ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ - R) ^ (2 - (n : ℝ)) * ∫ t, ‖f t‖ := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ :=
    inv_nonneg.2 (mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (volume_real_unitBall_pos n).le)
  rw [convolution_lsmul_swap, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (ae_of_all _ fun t => ?_)
  rw [norm_smul]
  by_cases ht : f t = 0
  · simp [ht]
  have htR := mem_closedBall_zero_iff.1 (hR ht)
  have hxt : ‖x‖ - R ≤ ‖x - t‖ := by linarith [norm_sub_norm_le x t]
  rw [newtonianKernel_def, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (by positivity))]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (norm_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hxt (by linarith)

/-- **Decay of the derivative of the Newtonian potential.** For `n ≠ 2` and `f` integrable on
`ℝⁿ` and vanishing off `closedBall 0 R`, at every point `x` with `R < ‖x‖`,

`‖D(Gₙ ⋆ f)(x)‖ ≤ (n ωₙ)⁻¹ (‖x‖ - R) ^ (1 - n) ∫ ‖f‖`,

where `ωₙ` is the volume of the unit ball. Off the support of `f` the derivative falls on the
kernel, whose gradient has size `(n ωₙ)⁻¹ ‖x - y‖ ^ (1 - n)`. -/
theorem norm_fderiv_newtonianKernel_convolution_le (hn : n ≠ 2) (hf : Integrable f) {R : ℝ}
    (hR : Function.support f ⊆ closedBall 0 R) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) :
    ‖fderiv ℝ (newtonianKernel n ⋆ f) x‖ ≤
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ - R) ^ (1 - (n : ℝ)) * ∫ t, ‖f t‖ := by
  set G := newtonianKernel n
  set Cd := ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  have hCd : 0 ≤ Cd := inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg n)
    (volume_real_unitBall_pos n).le)
  -- On the support of `f`, the gradient of the kernel at `z - y` is controlled by `‖z - y‖`.
  have hdG : ∀ {z y : EuclideanSpace ℝ (Fin n)} {r : ℝ}, 0 < r → f y ≠ 0 → r ≤ ‖z - y‖ →
      ‖fderiv ℝ G (z - y)‖ ≤ Cd * r ^ (1 - (n : ℝ)) := fun {z y r} hr hy hzy => by
    have hzy0 : z - y ≠ 0 := norm_pos_iff.1 (hr.trans_le hzy)
    have hn1 : (1 : ℝ) ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact (hzy0 (Subsingleton.elim _ _)).elim
      · exact_mod_cast h
    rw [norm_fderiv_newtonianKernel n hn hzy0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hzy (by linarith)) hCd
  have hfR : ∀ {y}, f y ≠ 0 → ‖y‖ ≤ R := fun hy => mem_closedBall_zero_iff.1 (hR hy)
  set δ := (‖x‖ - R) / 2 with hδdef
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hGm : Measurable G := by
    have hG : G = fun y => ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * ‖y‖ ^ (2 - (n : ℝ)) :=
      funext (newtonianKernel_def n)
    rw [hG]
    fun_prop
  have hFm : ∀ z, AEStronglyMeasurable (fun y => G (z - y) • f y) volume := fun z =>
    (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  -- Differentiate `z ↦ ∫ Gₙ(z - y) f(y) dy` under the integral on `ball x δ`.
  have hfd : HasFDerivAt (fun z => ∫ y, G (z - y) • f y)
      (∫ y, (fderiv ℝ G (x - y)).smulRight (f y)) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z y => G (z - y) • f y)
      (F' := fun z y => (fderiv ℝ G (z - y)).smulRight (f y))
      (bound := fun y => Cd * δ ^ (1 - (n : ℝ)) * ‖f y‖) (ball_mem_nhds x hδ)
      (Eventually.of_forall hFm) ?_ ?_ (ae_of_all _ fun y z hz => ?_) (hf.norm.const_mul _)
      (ae_of_all _ fun y z hz => ?_)
    · -- Integrability at `x`: the kernel is bounded on the compact ball containing the support.
      have hcont : ContinuousOn (fun y => G (x - y)) (closedBall 0 R) := fun y hy =>
        ((contDiffAt_newtonianKernel n (sub_ne_zero.2 fun h =>
          (mem_closedBall_zero_iff.1 hy).not_gt (by rwa [← h]))).continuousAt.comp
            (continuousAt_const.sub continuousAt_id)).continuousWithinAt
      obtain ⟨M, hM⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn hcont
      refine (hf.norm.const_mul M).mono' (hFm x) (ae_of_all _ fun y => ?_)
      by_cases hy : f y = 0
      · simp [hy]
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hM y (hR hy)) (norm_nonneg _)
    · exact (smulRightL ℝ (EuclideanSpace ℝ (Fin n)) F).aestronglyMeasurable_comp₂
        ((measurable_fderiv ℝ G).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        hf.aestronglyMeasurable
    · rw [norm_smulRight_apply]
      by_cases hy : f y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_right (hdG hδ hy ?_) (norm_nonneg _)
      have := mem_ball_iff_norm'.1 hz
      linarith [norm_sub_norm_le x z, norm_sub_norm_le z y, hfR hy, hδdef]
    · by_cases hy : f y = 0
      · simpa [hy] using hasFDerivAt_const (0 : F) z
      have hzy : z - y ≠ 0 := by
        have := mem_ball_iff_norm'.1 hz
        refine norm_pos_iff.1 ?_
        linarith [norm_sub_norm_le x z, norm_sub_norm_le z y, hfR hy, hδdef]
      exact ((((contDiffAt_newtonianKernel n hzy).differentiableAt (by norm_num)).hasFDerivAt
        ).comp z ((hasFDerivAt_id z).sub_const y)).smul_const (f y)
  have hconv : newtonianKernel n ⋆ f = fun z => ∫ y, G (z - y) • f y :=
    funext fun z => convolution_lsmul_swap
  rw [hconv, hfd.fderiv, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (ae_of_all _ fun y => ?_)
  rw [norm_smulRight_apply]
  by_cases hy : f y = 0
  · simp [hy]
  exact mul_le_mul_of_nonneg_right (hdG (z := x) (r := ‖x‖ - R) (by linarith) hy
    (by linarith [norm_sub_norm_le x y, hfR hy])) (norm_nonneg _)

/-- **The Newtonian potential vanishes at infinity.** For `n ≥ 3` and `f` continuous with compact
support on `ℝⁿ`, `(Gₙ ⋆ f) x → 0` as `x → ∞`. -/
theorem tendsto_newtonianKernel_convolution_cocompact (hn : 3 ≤ n) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    Tendsto (newtonianKernel n ⋆ f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set C : ℝ := ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      C * (‖x‖ - R) ^ (2 - (n : ℝ)) * ∫ t, ‖f t‖) (cocompact _) (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (n : ℝ) - 2) (by linarith)).comp
      (tendsto_atTop_add_const_right _ (-R)
        (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin n))))
    have hexp : -((n : ℝ) - 2) = 2 - n := by ring
    simpa [Function.comp_def, hexp, sub_eq_add_neg] using (h.const_mul C).mul_const (∫ t, ‖f t‖)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with x hx
  exact norm_newtonianKernel_convolution_le hn (hf.integrable_of_hasCompactSupport hc)
    ((subset_tsupport f).trans hR) hx

/-- Away from `x`, the second derivative of `y ↦ Gₙ(y - x)`, first in the direction `v` and then
in the direction `w`, is the Hessian `D²Gₙ(x - y)(v, w)`. -/
private theorem fderiv_fderiv_newtonianKernel_sub_apply {x y : EuclideanSpace ℝ (Fin n)}
    (hy : y ≠ x) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => newtonianKernel n (z - x)) y v) y w =
      iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] := by
  have hG2 := contDiffAt_newtonianKernel n (sub_ne_zero.2 hy)
  have hdG : DifferentiableAt ℝ (fderiv ℝ (newtonianKernel n)) (y - x) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hkfun : (fun y => fderiv ℝ (fun z => newtonianKernel n (z - x)) y v) =
      fun y => fderiv ℝ (newtonianKernel n) (y - x) v :=
    funext fun y => by rw [fderiv_comp_sub]
  rw [← iteratedFDeriv_two_newtonianKernel_neg, neg_sub, hkfun,
    fderiv_comp_sub (f := fun z => fderiv ℝ (newtonianKernel n) z v),
    fderiv_clm_apply_const_apply hdG, iteratedFDeriv_two_apply]
  exact ContDiffAt.isSymmSndFDerivAt hG2 (by simp) w v

/-- **Second derivatives of the Newtonian potential off the support.** If `f` is `C²` with
compact support on `ℝⁿ` and `x ∉ tsupport f`, then

`D²(Gₙ ⋆ f)(x)(v, w) = ∫ D²Gₙ(x - y)(v, w) f(y) dy`.

Near `x` the kernel `y ↦ Gₙ(x - y)` is smooth on the support of `f`, so the two derivatives move
from `f` onto the kernel by integration by parts. -/
theorem iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport f) (v w : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ f) x ![v, w] =
      ∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • f y := by
  set G := newtonianKernel n
  have hG := locallyIntegrable_newtonianKernel n
  set fw : EuclideanSpace ℝ (Fin n) → F := fun y => fderiv ℝ f y w
  have hfw : ContDiff ℝ 1 fw := (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hcw : HasCompactSupport fw := hc.fderiv_apply (𝕜 := ℝ) w
  have hu : ContDiff ℝ 2 (G ⋆ f) := contDiff_newtonianKernel_convolution hf hc
  -- The derivatives of the convolution fall on `f`.
  have h₁ : (fun y => fderiv ℝ (G ⋆ f) y w) = G ⋆ fw := funext fun y =>
    hc.fderiv_convolution_right_apply (lsmul ℝ ℝ) hG (hf.of_le (by norm_num)) y w
  have hdu : DifferentiableAt ℝ (fderiv ℝ (G ⋆ f)) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← fderiv_clm_apply_const_apply hdu w v, h₁,
    hcw.fderiv_convolution_right_apply (lsmul ℝ ℝ) hG hfw x v, convolution_lsmul_swap]
  -- The kernel `k y = Gₙ(y - x)` is `C²` away from `x`, in particular near `tsupport f`.
  set k : EuclideanSpace ℝ (Fin n) → ℝ := fun y => G (y - x)
  have hk : ∀ y, y ≠ x → ContDiffAt ℝ 2 k y := fun y hy =>
    (contDiffAt_newtonianKernel n (sub_ne_zero.2 hy)).comp y (contDiffAt_id.sub contDiffAt_const)
  have hne : ∀ y ∈ tsupport f, y ≠ x := fun y hy hyx => hx (hyx ▸ hy)
  have hkv : ∀ y, y ≠ x → ContDiffAt ℝ 1 (fun y => fderiv ℝ k y v) y := fun y hy =>
    ((hk y hy).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hsub : tsupport fw ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ w
  -- Integrability: every integrand is a function continuous off `x` times a continuous function
  -- with compact support in `tsupport f`, which does not contain `x`.
  have hint : ∀ {a : EuclideanSpace ℝ (Fin n) → ℝ} {b : EuclideanSpace ℝ (Fin n) → F},
      ContinuousOn a {x}ᶜ → Continuous b → HasCompactSupport b → tsupport b ⊆ tsupport f →
        Integrable fun y => a y • b y := fun ha hb hbc hbf =>
    ((ha.smul hb.continuousOn).continuous_of_tsupport_subset isOpen_compl_singleton
      ((tsupport_smul_subset_right _ _).trans fun y hy => hne y (hbf hy))
      ).integrable_of_hasCompactSupport hbc.smul_left
  have hkc : ContinuousOn k {x}ᶜ := fun y hy => (hk y hy).continuousAt.continuousWithinAt
  have hkvc : ContinuousOn (fun y => fderiv ℝ k y v) {x}ᶜ := fun y hy =>
    (hkv y hy).continuousAt.continuousWithinAt
  have hkwc : ContinuousOn (fun y => fderiv ℝ (fun y => fderiv ℝ k y v) y w) {x}ᶜ :=
    fun y hy => (((hkv y hy).fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hfwv : Continuous fun y => fderiv ℝ fw y v :=
    (hfw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsub' : tsupport (fun y => fderiv ℝ fw y v) ⊆ tsupport f :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsub
  have hkx : ∀ y, newtonianKernel n (x - y) = k y := fun y => newtonianKernel_sub_comm n x y
  simp_rw [hkx]
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (hint hkvc hfw.continuous hcw hsub)
      (hint hkc hfwv (hcw.fderiv_apply (𝕜 := ℝ) v) hsub')
      (hint hkc hfw.continuous hcw hsub)
      (fun y hy => (hk y (hne y (hsub hy))).differentiableAt (by norm_num))
      (fun y _ => hfw.differentiable one_ne_zero y),
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (f := fun y => fderiv ℝ k y v) (g := f)
      (hint hkwc hf.continuous hc subset_rfl)
      (hint hkvc hfw.continuous hcw hsub)
      (hint hkvc hf.continuous hc subset_rfl)
      (fun y hy => (hkv y (hne y hy)).differentiableAt one_ne_zero)
      (fun y _ => hf.differentiable (by norm_num) y), neg_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ tsupport f
  · dsimp only
    rw [fderiv_fderiv_newtonianKernel_sub_apply (hne y hy)]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Uniqueness for Poisson's equation.** For `n ≥ 3` and `f` of class `C²` with compact support
on `ℝⁿ`, the Newtonian potential `Gₙ ⋆ f` is the only `C²` solution `v` of `-Δv = f` that tends to
zero at infinity. -/
theorem eq_newtonianKernel_convolution_of_laplacian_eq_neg [CompleteSpace F] (hn : 3 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {v : EuclideanSpace ℝ (Fin n) → F}
    (hv : ContDiff ℝ 2 v) (hΔ : Δ v = -f)
    (hv₀ : Tendsto v (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)) :
    v = newtonianKernel n ⋆ f := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hu := contDiff_newtonianKernel_convolution hf hc
  have hw : HarmonicOnNhd (v - newtonianKernel n ⋆ f) univ := fun x _ =>
    ⟨(hv.sub hu).contDiffAt, Eventually.of_forall fun y => by
      rw [hv.contDiffAt.laplacian_sub hu.contDiffAt, hΔ,
        laplacian_newtonianKernel_convolution hn hf hc, sub_self, Pi.zero_apply]⟩
  have hw₀ := hv₀.sub (tendsto_newtonianKernel_convolution_cocompact hn hf.continuous hc)
  rw [sub_zero] at hw₀
  exact sub_eq_zero.1 (hw.eq_zero_of_tendsto_cocompact hw₀)

end TauCeti
