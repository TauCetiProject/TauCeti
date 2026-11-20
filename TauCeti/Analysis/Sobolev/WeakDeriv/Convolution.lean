/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.CompactSupport

/-!
# Weak derivatives of convolutions with a singular kernel

Let `K` be a locally integrable kernel on a finite-dimensional real normed space with a locally
integrable derivative `K'`, such as a fundamental solution, and suppose that integration by parts
against `K` holds across its singularity: for every `C¹` function `g` with compact support and
every pole `t`, `∫ ∂ᵥg (x) K(x - t) dx = -∫ g(x) K'(x - t) v dx`. Then for every integrable `f`
with compact support the potential `K ⋆ f` has weak derivative `K' ⋆ f` on every open set
(`TauCeti.hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub`).

Pairing the potential with `∂ᵥg` and exchanging the integrals
(`MeasureTheory.integral_mul_convolution_eq_integral_mul_integral_left_comp_sub`) moves the
derivative onto the kernel with pole `t`, where integration by parts applies; exchanging the
integrals back gives the pairing of `g` with `K' ⋆ f`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1 (the gradient of the Newtonian potential is the potential of the kernel's gradient).
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace ContinuousLinearMap
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [μ.IsNegInvariant]

/-- **The weak derivative of the potential of a singular kernel.** Let `K` be locally integrable
with locally integrable `K'`, and suppose `K'` is the derivative of `K` in the sense of
integration by parts with any pole `t`: `∫ ∂ᵥg (x) K(x - t) dx = -∫ g(x) K'(x - t) v dx` for
every `C¹` function `g` with compact support. Then for `f` integrable with compact support the
convolution `K ⋆ f` has weak derivative `K' ⋆ f`, `x ↦ ∫ f(x - y) • K'(y) dy`, on every open set. -/
theorem hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub {K : E → ℝ}
    {K' : E → E →L[ℝ] ℝ} {f : E → ℝ} (hK : LocallyIntegrable K μ)
    (hK' : LocallyIntegrable K' μ)
    (hibp : ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ v t,
      ∫ x, fderiv ℝ g x v * K (x - t) ∂μ = -∫ x, g x * K' (x - t) v ∂μ)
    (hf : Integrable f μ) (hfc : HasCompactSupport f) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (K ⋆[lsmul ℝ ℝ, μ] f) (K' ⋆[(lsmul ℝ ℝ).flip, μ] f) := by
  refine hasWeakFDerivOn_of_forall_integral_fderiv_smul
    (hfc.locallyIntegrable_convolution_right _ hK hf)
    (hfc.locallyIntegrable_convolution_right _ hK' hf) (fun g hg hgc v ↦ ?_) Ω
  have hKv : LocallyIntegrableOn (fun z ↦ K' z v) univ μ :=
    (ContinuousLinearMap.apply ℝ ℝ v).locallyIntegrableOn_comp (hK'.locallyIntegrableOn univ)
  have hgv : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- Where the operator-valued convolution exists, it may be evaluated at `v` under the integral.
  have hU : (fun x ↦ (K' ⋆[(lsmul ℝ ℝ).flip, μ] f) x v) =ᵐ[μ]
      f ⋆[lsmul ℝ ℝ, μ] fun z ↦ K' z v := by
    filter_upwards [hfc.ae_convolutionExistsAt_right (lsmul ℝ ℝ).flip hK' hf] with x hx
    rw [convolution_def, ContinuousLinearMap.integral_apply hx, convolution_lsmul_swap]
    simp
  calc ∫ x, fderiv ℝ g x v • (K ⋆[lsmul ℝ ℝ, μ] f) x ∂μ
      = ∫ t, f t * ∫ x, fderiv ℝ g x v * K (x - t) ∂μ ∂μ :=
        integral_mul_convolution_eq_integral_mul_integral_left_comp_sub hgv
          (hgc.fderiv_apply ℝ v) hK hf hfc
    _ = -∫ t, f t * ∫ x, g x * K' (x - t) v ∂μ ∂μ := by
        simp_rw [hibp g hg hgc v, mul_neg, integral_neg]
    _ = -∫ x, g x * (f ⋆[lsmul ℝ ℝ, μ] fun z ↦ K' z v) x ∂μ := by
        rw [integral_mul_convolution_eq_integral_mul_integral_comp_sub hg.continuous hgc hf hfc hKv
          fun _ _ _ _ ↦ mem_univ _]
    _ = -∫ x, g x • (K' ⋆[(lsmul ℝ ℝ).flip, μ] f) x v ∂μ := by
        refine congrArg Neg.neg (integral_congr_ae ?_)
        filter_upwards [hU] with x hx
        rw [smul_eq_mul, hx]

end TauCeti
