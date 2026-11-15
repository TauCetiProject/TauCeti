/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Analysis.Sobolev.WeakDeriv.Convolution

/-!
# The planar Newtonian potential of a continuous source gains one derivative

For a real function `g` on `ℂ` with compact support, the Newtonian potential `u = G ⋆ g` with the
logarithmic kernel `G = TauCeti.planarNewtonianKernel` is `C^k` when `g` is `C^k`
(`TauCeti.contDiff_planarNewtonianKernel_convolution`). This file shows that it is one derivative
smoother, already for continuous `g`, and that it solves Poisson's equation `-Δu = g` in the sense
of distributions without any differentiability of `g`.

* The weak derivative of `u` is the convolution of `g` with the locally integrable derivative of
  the kernel, `∂ᵥu = (∂ᵥG) ⋆ g` (`TauCeti.hasWeakFDerivOn_planarNewtonianKernel_convolution`). For
  `g` of class `C^k` this convolution is again `C^k`, so `u` is `C^(k+1)`
  (`TauCeti.contDiff_succ_planarNewtonianKernel_convolution`). For `k = 0` this is the classical
  fact that the Newtonian potential of a continuous function is `C¹`.
* For a `C²` test function `φ` with compact support, `∫ Δφ · u = -∫ φ g`
  (`TauCeti.integral_laplacian_mul_planarNewtonianKernel_convolution`).

Both statements come from Fubini's theorem, which moves the pairing with a test function onto the
kernel, where the distributional identities `-ΔG = δ`
(`TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`) and the integration by parts formula
`TauCeti.integral_planarNewtonianKernel_sub_mul_fderiv_eq_neg_fderiv_mul` apply. The gain of one
derivative is what drives the interior regularity bootstrap for semilinear Poisson equations in the
plane.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.1.
-/

public section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped Convolution ContDiff

variable {g : ℂ → ℝ}

/-- **The Newtonian potential of a continuous source solves Poisson's equation weakly.** For `g`
continuous with compact support on `ℂ` and every `C²` function `φ` with compact support,
`∫ Δφ · (G ⋆ g) = -∫ φ g`; that is, `-Δ (G ⋆ g) = g` in the sense of distributions. -/
theorem integral_laplacian_mul_planarNewtonianKernel_convolution (hg : Continuous g)
    (hgc : HasCompactSupport g) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, Δ φ x * (planarNewtonianKernel ⋆ g) x = -∫ x, φ x * g x := by
  rw [integral_mul_convolution_eq_integral_mul_integral_left_comp_sub hφ.continuous_laplacian
    hφc.laplacian locallyIntegrable_planarNewtonianKernel (hg.integrable_of_hasCompactSupport hgc)
    hgc, ← integral_neg]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [integral_laplacian_mul_planarNewtonianKernel_sub hφ hφc t]
  ring

/-- **The weak derivative of the Newtonian potential of a continuous source.** For `g` continuous
with compact support on `ℂ`, the potential `G ⋆ g` has weak derivative `(∂G) ⋆ g`, the convolution
of `g` with the locally integrable derivative of the kernel, on every open set. -/
theorem hasWeakFDerivOn_planarNewtonianKernel_convolution (hg : Continuous g)
    (hgc : HasCompactSupport g) (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (planarNewtonianKernel ⋆ g)
      (fderiv ℝ planarNewtonianKernel ⋆[(lsmul ℝ ℝ).flip] g) :=
  hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub
    locallyIntegrable_planarNewtonianKernel locallyIntegrable_fderiv_planarNewtonianKernel
    (fun φ hφ hφc v t ↦ by
      simpa only [mul_comm] using
        integral_planarNewtonianKernel_sub_mul_fderiv_eq_neg_fderiv_mul hφ hφc v t)
    (hg.integrable_of_hasCompactSupport hgc) hgc Ω

/-- **The Newtonian potential gains one derivative.** For `g` of class `C^k` with compact support
on `ℂ`, the potential `G ⋆ g` is of class `C^(k+1)`. For `k = 0`: the Newtonian potential of a
continuous function with compact support is `C¹`. -/
theorem contDiff_succ_planarNewtonianKernel_convolution {k : ℕ∞} (hg : ContDiff ℝ k g)
    (hgc : HasCompactSupport g) :
    ContDiff ℝ ((k : ℕ∞ω) + 1) (planarNewtonianKernel ⋆ g) := by
  have hc : Continuous g := hg.continuous
  have h := (hasWeakFDerivOn_planarNewtonianKernel_convolution hc hgc ⊤).contDiffOn_succ
    (hgc.continuous_convolution_right _ locallyIntegrable_planarNewtonianKernel hc).continuousOn
    (hgc.contDiff_convolution_right _ locallyIntegrable_fderiv_planarNewtonianKernel hg).contDiffOn
  rwa [Opens.coe_top, contDiffOn_univ] at h

end TauCeti
