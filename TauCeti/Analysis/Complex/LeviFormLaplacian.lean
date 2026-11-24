/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues

/-!
# The trace of the Levi form is a quarter of the Laplacian

On a finite-dimensional complex inner product space `E`, view `E` as a real inner product space
with `⟪v, w⟫_ℝ = Re ⟪v, w⟫_ℂ`. A complex orthonormal basis `b` gives the real orthonormal basis
`(b j, I • b j)` (`OrthonormalBasis.complexToReal`). Evaluating the Laplacian `Δ f` in this basis
and the real part of the diagonal of the Levi form through `TauCeti.re_leviForm_apply` gives
`∑ⱼ Re (leviForm f x (b j) (b j)) = Δ f x / 4`
(`TauCeti.sum_re_leviForm_apply_self`). In the normalization `H_{i∂∂bar f} = 2 L_f` of the
ComplexHessianEquations roadmap, the relative eigenvalues of `2 L_f(x)` with respect to the inner
product therefore sum to `Δ f x / 2` (`TauCeti.sum_relEigenvalues_two_smul_leviForm`): the complex
Laplacian `Δ_ω f = ∑ⱼ λⱼ[i∂∂bar f]` of the standard metric is half the Euclidean Laplacian.

The real inner product structure `InnerProductSpace.complexToReal` is enabled locally.

## Main definitions

* `OrthonormalBasis.complexToReal`: the real orthonormal basis `(b j, I • b j)` of a complex inner
  product space.

## Main results

* `LinearMap.IsSymm.sum_relEigenvalues_eq_sum_re_apply`: the relative eigenvalues of a Hermitian
  form sum to the real parts of its diagonal entries in any orthonormal basis.
* `TauCeti.sum_re_leviForm_apply_self`: the trace of the Levi form is `Δ f x / 4`.
* `TauCeti.sum_relEigenvalues_two_smul_leviForm`: the relative eigenvalues of `2 L_f(x)` sum to
  `Δ f x / 2`.
-/

public section

open Complex Module
open scoped InnerProductSpace Laplacian

namespace LinearMap.IsSymm

variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- The relative eigenvalues of a Hermitian form sum to the sum of the real parts of its diagonal
entries in any orthonormal basis. -/
theorem sum_relEigenvalues_eq_sum_re_apply (ha : a.IsSymm) {n : ℕ} (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, ha.relEigenvalues hn i = ∑ j, RCLike.re (a (b j) (b j)) := by
  have hsum := congrArg RCLike.re (ha.sum_relEigenvalues hn)
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum, map_sum] at hsum
  simpa only [RCLike.ofReal_re, LinearMap.inner_toSesqForm_symm_apply] using hsum

end LinearMap.IsSymm

section Complex

attribute [local instance] InnerProductSpace.complexToReal

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The family `(b j, I • b j)` is orthonormal for the real inner product `Re ⟪·, ·⟫`. -/
theorem OrthonormalBasis.orthonormal_sumElim_I_smul (b : OrthonormalBasis ι ℂ E) :
    Orthonormal ℝ (Sum.elim (⇑b) fun j ↦ I • b j) := by
  classical
  rw [orthonormal_iff_ite]
  rintro (i | i) (j | j) <;>
    simp [real_inner_eq_re_inner, inner_smul_left, inner_smul_right, b.inner_eq_ite,
      apply_ite]

/-- Every vector is a real combination of the vectors `b j` and `I • b j`. -/
theorem OrthonormalBasis.top_le_span_sumElim_I_smul (b : OrthonormalBasis ι ℂ E) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim (⇑b) fun j ↦ I • b j)) := by
  intro x _
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  have hc : b.repr x j • b j = (b.repr x j).re • b j + (b.repr x j).im • (I • b j) := by
    conv_lhs => rw [← Complex.re_add_im (b.repr x j)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hc]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl j, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr j, rfl⟩))

/-- The **real orthonormal basis** `(b j, I • b j)`, indexed by `ι ⊕ ι`, of a complex inner product
space with complex orthonormal basis `b`, for the real inner product `Re ⟪·, ·⟫`. -/
noncomputable def OrthonormalBasis.complexToReal (b : OrthonormalBasis ι ℂ E) :
    OrthonormalBasis (ι ⊕ ι) ℝ E :=
  OrthonormalBasis.mk b.orthonormal_sumElim_I_smul b.top_le_span_sumElim_I_smul

@[simp]
theorem OrthonormalBasis.complexToReal_inl (b : OrthonormalBasis ι ℂ E) (j : ι) :
    b.complexToReal (.inl j) = b j := by
  simp [OrthonormalBasis.complexToReal]

@[simp]
theorem OrthonormalBasis.complexToReal_inr (b : OrthonormalBasis ι ℂ E) (j : ι) :
    b.complexToReal (.inr j) = I • b j := by
  simp [OrthonormalBasis.complexToReal]

namespace TauCeti

variable [FiniteDimensional ℂ E] {f : E → ℝ} {x : E}

/-- **The trace of the Levi form is a quarter of the Laplacian.** For any real function `f` and
any complex orthonormal basis `b`, `∑ⱼ Re (leviForm f x (b j) (b j)) = Δ f x / 4`, where `Δ` is
the Laplacian for the real inner product `Re ⟪·, ·⟫`. No differentiability is needed: both sides
are read off the same second derivative. -/
theorem sum_re_leviForm_apply_self (b : OrthonormalBasis ι ℂ E) :
    ∑ j, (leviForm f x (b j) (b j)).re = Δ f x / 4 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b.complexToReal]
  dsimp only
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [re_leviForm_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp

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

end Complex
