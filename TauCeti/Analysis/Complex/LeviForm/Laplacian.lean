/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.LeviForm.Basic
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Basic

/-!
# The trace of the Levi form is a quarter of the Laplacian

On a finite-dimensional complex inner product space `E`, view `E` as a real inner product space
with `⟪v, w⟫_ℝ = Re ⟪v, w⟫_ℂ`. A complex orthonormal basis `b` gives the real orthonormal basis
`(b j, I • b j)` (`OrthonormalBasis.complexToReal`). Evaluating the Laplacian `Δ f` in this basis
and the real part of the diagonal of the Levi form through
`LinearMap.BilinForm.sum_re_leviForm_apply_self` gives
`∑ⱼ Re (leviForm f x (b j) (b j)) = Δ f x / 4`
(`TauCeti.sum_re_leviForm_apply_self`). With the convention that the Hermitian form of
`i∂∂bar f` is `2 L_f`, the relative eigenvalues of `2 L_f(x)` with respect to the inner product
therefore sum to `Δ f x / 2` (`TauCeti.sum_relEigenvalues_two_smul_leviForm`): the complex
Laplacian `Δ_ω f = ∑ⱼ λⱼ[i∂∂bar f]` of the standard metric is half the Euclidean Laplacian.

The real inner product structure `InnerProductSpace.complexToReal` is enabled locally.

## Main results

* `TauCeti.sum_re_leviForm_apply_self`: the trace of the Levi form is `Δ f x / 4`.
* `TauCeti.sum_relEigenvalues_two_smul_leviForm`: the relative eigenvalues of `2 L_f(x)` sum to
  `Δ f x / 2`.
-/

public section

open Complex Module
open scoped InnerProductSpace Laplacian

attribute [local instance] InnerProductSpace.complexToReal

namespace TauCeti

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {f : E → ℝ} {x : E}

/-- **The trace of the Levi form is a quarter of the Laplacian.** For any real function `f` and
any complex orthonormal basis `b`, `∑ⱼ Re (leviForm f x (b j) (b j)) = Δ f x / 4`, where `Δ` is
the Laplacian for the real inner product `Re ⟪·, ·⟫`. No differentiability is needed: both sides
are read off the same second derivative. -/
theorem sum_re_leviForm_apply_self (b : OrthonormalBasis ι ℂ E) :
    ∑ j, (leviForm f x (b j) (b j)).re = Δ f x / 4 := by
  have h := (fderiv ℝ (fderiv ℝ f) x).toBilinForm.sum_re_leviForm_apply_self b.toBasis
  rw [← OrthonormalBasis.toBasis_complexToReal] at h
  simp only [OrthonormalBasis.coe_toBasis] at h
  rw [leviForm_def, h,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b.complexToReal]
  simp [iteratedFDeriv_two_apply]

/-- **The complex Laplacian of the standard metric.** The relative eigenvalues of `2 L_f(x)`, the
Hermitian form of `i∂∂bar f` at `x`, with respect to the inner product sum to `Δ f x / 2`, half the
Laplacian for the real inner product `Re ⟪·, ·⟫`. -/
theorem sum_relEigenvalues_two_smul_leviForm {n : ℕ} (hn : finrank ℂ E = n)
    (h : ((2 : ℂ) • leviForm f x).IsSymm) :
    ∑ i, h.relEigenvalues hn i = Δ f x / 2 := by
  rw [h.sum_relEigenvalues_eq_sum_re_apply hn (stdOrthonormalBasis ℂ E)]
  simp only [LinearMap.smul_apply, smul_eq_mul, RCLike.re_to_complex, mul_re, re_ofNat,
    im_ofNat, zero_mul, sub_zero]
  rw [← Finset.mul_sum, sum_re_leviForm_apply_self]
  ring

end TauCeti
