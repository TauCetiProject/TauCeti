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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution

/-!
# The Newtonian potential solves Poisson's equation

For `f : ℝⁿ → F` with compact support, the **Newtonian potential** of `f` is the convolution
`u = Gₙ ⋆ f`, `u x = ∫ Gₙ(x - y) f(y) dy`, of `f` with the Newtonian kernel
`Gₙ = TauCeti.newtonianKernel n`. For `n ≥ 3` and `f` of class `C²` with compact support:

* `u` is as smooth as `f` (no restriction on `n` is needed here);
* `u` solves **Poisson's equation** `-Δu = f` on all of `ℝⁿ`;
* `u` is harmonic off the support of `f`;
* `u` tends to zero at infinity (already for continuous `f` with compact support);
* `u` is the **unique** `C²` solution of `-Δv = f` that tends to zero at infinity.

The Laplacian falls on `f` under the convolution (`HasCompactSupport.laplacian_convolution_right`),
and the distributional identity `-ΔGₙ = δ` (`TauCeti.integral_laplacian_mul_newtonianKernel_sub`)
evaluates the result. Uniqueness holds because a harmonic function on `ℝⁿ` that vanishes at
infinity is zero (`InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`).

## Main declarations

* `TauCeti.contDiff_newtonianKernel_convolution`: `Gₙ ⋆ f` is `C^k` when `f` is `C^k` with
  compact support.
* `TauCeti.laplacian_newtonianKernel_convolution`: `Δ (Gₙ ⋆ f) = -f`.
* `TauCeti.harmonicOnNhd_newtonianKernel_convolution`: `Gₙ ⋆ f` is harmonic off `tsupport f`.
* `TauCeti.tendsto_newtonianKernel_convolution_cocompact`: `Gₙ ⋆ f → 0` at infinity.
* `TauCeti.eq_newtonianKernel_convolution_of_laplacian_eq_neg`: uniqueness among solutions
  vanishing at infinity.

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

/-- **The Newtonian potential vanishes at infinity.** For `n ≥ 3` and `f` continuous with compact
support on `ℝⁿ`, `(Gₙ ⋆ f) x → 0` as `x → ∞`. -/
theorem tendsto_newtonianKernel_convolution_cocompact (hn : 3 ≤ n) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    Tendsto (newtonianKernel n ⋆ f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set C : ℝ := ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  have hC : 0 ≤ C := inv_nonneg.2 (mul_nonneg (mul_nonneg (by linarith) (by linarith))
    (volume_real_unitBall_pos n).le)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hfi : Integrable (fun t => ‖f t‖) := hf.norm.integrable_of_hasCompactSupport hc.norm
  -- The pointwise bound off a large ball.
  have hbound : ∀ x : EuclideanSpace ℝ (Fin n), R + 1 ≤ ‖x‖ →
      ‖(newtonianKernel n ⋆ f) x‖ ≤ C * (‖x‖ - R) ^ (2 - (n : ℝ)) * ∫ t, ‖f t‖ := by
    intro x hx
    rw [convolution_lsmul_swap, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hfi.const_mul _) (ae_of_all _ fun t => ?_)
    rw [norm_smul]
    by_cases ht : t ∈ tsupport f
    · have htR := mem_closedBall_zero_iff.1 (hR ht)
      have hxt : ‖x‖ - R ≤ ‖x - t‖ := by linarith [norm_sub_norm_le x t]
      rw [newtonianKernel_def, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (by positivity))]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (norm_nonneg _)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hxt (by linarith)
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      C * (‖x‖ - R) ^ (2 - (n : ℝ)) * ∫ t, ‖f t‖) (cocompact _) (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (n : ℝ) - 2) (by linarith)).comp
      (tendsto_atTop_add_const_right _ (-R)
        (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin n))))
    have hexp : -((n : ℝ) - 2) = 2 - n := by ring
    simpa [Function.comp_def, hexp, sub_eq_add_neg] using (h.const_mul C).mul_const (∫ t, ‖f t‖)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 1)] with x hx
  exact hbound x hx

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
