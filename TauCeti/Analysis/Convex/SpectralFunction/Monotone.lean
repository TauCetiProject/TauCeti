/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.InnerProductSpace.CourantFischer
import TauCeti.Analysis.InnerProductSpace.Positive.Basic

/-!
# Monotonicity of spectral domains and spectral functions

Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, where `Γ_n` is the open positive orthant: adding a vector
with positive coordinates to a point of `Γ` stays in `Γ`. Then `Γ` is upward closed for the
componentwise order. If `f` is differentiable on `Γ` with nonnegative partial derivatives
`∂_i f`, then `f` is monotone on `Γ`, and strictly monotone if the partial derivatives are
positive: by the mean value theorem on the segment from `μ ≤ ν`, `f ν - f μ` is
`Σ_i (ν - μ)_i ∂_i f(z) ≥ 0` at some point `z` of the segment.

For symmetric operators `S ≤ T` in the Loewner order on a finite-dimensional inner product space,
the decreasingly sorted eigenvalue vectors satisfy `λ(S) ≤ λ(T)` componentwise
(`LinearMap.IsSymmetric.eigenvalue_mono`). So the spectral domain `{T | λ(T) ∈ Γ}` is upward
closed, the spectral function `T ↦ f(λ(T))` is monotone, and it is strictly monotone when the
partial derivatives of `f` are positive: if `λ(S) = λ(T)`, then `T - S ≥ 0` has trace zero, so
`S = T` (`LinearMap.IsSymmetric.eq_of_re_inner_le_of_eigenvalues_eq`).

Convexity of `Γ` is not used, and `Γ` need not be symmetric for these statements. The results on
`ℝⁿ` are stated for `ι → ℝ` with `ι` finite; upward closure holds for any index type `ι`.

## Main results

* `TauCeti.mem_of_le_of_forall_add_mem`: `Γ` is upward closed.
* `TauCeti.le_of_le_of_forall_fderiv_single_nonneg`: `f μ ≤ f ν` for `μ ≤ ν`, `μ ∈ Γ`, when
  every `∂_i f ≥ 0` on `Γ`.
* `TauCeti.lt_of_le_of_ne_of_forall_fderiv_single_pos`: `f μ < f ν` for `μ ≤ ν`, `μ ≠ ν`, when
  every `∂_i f > 0` on `Γ`.
* `LinearMap.IsSymmetric.eigenvalues_mem_of_re_inner_le`: the spectral domain is upward closed in
  the Loewner order.
* `LinearMap.IsSymmetric.apply_eigenvalues_le_of_re_inner_le` and
  `LinearMap.IsSymmetric.apply_eigenvalues_lt_of_re_inner_le_of_ne`: the spectral function is
  monotone, and strictly monotone for positive partial derivatives.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in *Global
  theory of minimal surfaces*, Clay Math. Proc. **2** (2005), 283–309, Theorem 1.4.
-/

public section

open Module Set
open scoped InnerProductSpace

namespace TauCeti

variable {ι : Type*} {Γ : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ} {μ ν : ι → ℝ}

/-- **Upward closure.** If `Γ ⊆ ℝ^ι` is open and adding a vector with positive coordinates to a
point of `Γ` stays in `Γ`, then `Γ` is upward closed for the componentwise order. -/
theorem mem_of_le_of_forall_add_mem (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : ι → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hμ : μ ∈ Γ) (hle : μ ≤ ν) :
    ν ∈ Γ := by
  -- Move down from `μ` by a small multiple of `(1, …, 1)`, staying in `Γ`, and then up to `ν`.
  have hc : Continuous fun t : ℝ ↦ μ - fun _ : ι ↦ t :=
    continuous_const.sub (continuous_pi fun _ ↦ continuous_id)
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), μ - (fun _ ↦ t) ∈ Γ :=
    nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds (by
      rw [← Pi.zero_def, sub_zero]
      exact hΓo.mem_nhds hμ))
  obtain ⟨t, hmem, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have h := hΓ _ hmem (ν - μ + (fun _ ↦ t)) fun i ↦ by
    have := hle i
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [mem_Ioi.mp ht]
  rwa [sub_add_add_cancel, add_sub_cancel] at h

/-- **Mean value theorem along a segment.** For `μ ∈ Γ` and `ν ≥ μ`, the segment from `μ` to `ν`
lies in `Γ`, and `f ν - f μ = Σ_i (ν i - μ i) ∂_i f(z)` for some `z ∈ Γ`. -/
private theorem exists_mem_sub_eq_sum_fderiv_single [Fintype ι] [DecidableEq ι] (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : ι → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hμ : μ ∈ Γ) (hle : μ ≤ ν) :
    ∃ z ∈ Γ, f ν - f μ = ∑ i, (ν i - μ i) * fderiv ℝ f z (Pi.single i 1) := by
  have hsub : segment ℝ μ ν ⊆ Γ := by
    rw [segment_eq_image']
    rintro _ ⟨t, ht, rfl⟩
    refine mem_of_le_of_forall_add_mem hΓo hΓ hμ fun i ↦ ?_
    have := hle i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [ht.1]
  obtain ⟨z, hz, h⟩ := domain_mvt (f' := fderiv ℝ f)
    (fun z hz ↦ ((hf z (hsub hz)).differentiableAt
      (hΓo.mem_nhds (hsub hz))).hasFDerivAt.hasFDerivWithinAt)
    (convex_segment μ ν) (left_mem_segment ℝ μ ν) (right_mem_segment ℝ μ ν)
  refine ⟨z, hsub hz, h.trans ?_⟩
  conv_lhs => rw [pi_eq_sum_univ' (ν - μ)]
  simp only [map_sum, map_smul, smul_eq_mul, Pi.sub_apply]

/-- **Monotonicity of `f`.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let `f` be
differentiable on `Γ` with nonnegative partial derivatives there. Then `f μ ≤ f ν` whenever
`μ ∈ Γ` and `μ ≤ ν`. -/
theorem le_of_le_of_forall_fderiv_single_nonneg [Finite ι] [DecidableEq ι] (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : ι → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hf' : ∀ μ ∈ Γ, ∀ i, 0 ≤ fderiv ℝ f μ (Pi.single i 1)) (hμ : μ ∈ Γ) (hle : μ ≤ ν) :
    f μ ≤ f ν := by
  have := Fintype.ofFinite ι
  obtain ⟨z, hz, h⟩ := exists_mem_sub_eq_sum_fderiv_single hΓo hΓ hf hμ hle
  rw [← sub_nonneg, h]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (sub_nonneg.mpr (hle i)) (hf' z hz i)

/-- **Strict monotonicity of `f`.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let `f` be
differentiable on `Γ` with positive partial derivatives there. Then `f μ < f ν` whenever `μ ∈ Γ`,
`μ ≤ ν` and `μ ≠ ν`. -/
theorem lt_of_le_of_ne_of_forall_fderiv_single_pos [Finite ι] [DecidableEq ι] (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : ι → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hf' : ∀ μ ∈ Γ, ∀ i, 0 < fderiv ℝ f μ (Pi.single i 1)) (hμ : μ ∈ Γ) (hle : μ ≤ ν)
    (hne : μ ≠ ν) : f μ < f ν := by
  have := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ : ∃ j, μ j ≠ ν j := Function.ne_iff.mp hne
  obtain ⟨z, hz, h⟩ := exists_mem_sub_eq_sum_fderiv_single hΓo hΓ hf hμ hle
  rw [← sub_pos, h]
  exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (sub_nonneg.mpr (hle i)) (hf' z hz i).le)
    ⟨j, Finset.mem_univ _, mul_pos (sub_pos.mpr ((hle j).lt_of_ne hj)) (hf' z hz j)⟩

end TauCeti

namespace LinearMap.IsSymmetric

open TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E} {n : ℕ} {Γ : Set (Fin n → ℝ)}
  {f : (Fin n → ℝ) → ℝ}

/-- **Upward closure of spectral domains.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`. If `S ≤ T` in
the Loewner order and the sorted eigenvalue vector `λ(S)` lies in `Γ`, then so does `λ(T)`. -/
theorem eigenvalues_mem_of_re_inner_le (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (hST : ∀ x, RCLike.re ⟪S x, x⟫_𝕜 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hΓo : IsOpen Γ) (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ)
    (hSΓ : hS.eigenvalues hn ∈ Γ) : hT.eigenvalues hn ∈ Γ :=
  mem_of_le_of_forall_add_mem hΓo hΓ hSΓ fun k ↦ eigenvalue_mono hS hT hn hST k

/-- **Monotonicity of spectral functions.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let `f`
be differentiable on `Γ` with nonnegative partial derivatives there. If `S ≤ T` in the Loewner
order and `λ(S) ∈ Γ`, then `f(λ(S)) ≤ f(λ(T))`. -/
theorem apply_eigenvalues_le_of_re_inner_le (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (hST : ∀ x, RCLike.re ⟪S x, x⟫_𝕜 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hΓo : IsOpen Γ) (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ)
    (hf : DifferentiableOn ℝ f Γ) (hf' : ∀ μ ∈ Γ, ∀ i, 0 ≤ fderiv ℝ f μ (Pi.single i 1))
    (hSΓ : hS.eigenvalues hn ∈ Γ) : f (hS.eigenvalues hn) ≤ f (hT.eigenvalues hn) :=
  le_of_le_of_forall_fderiv_single_nonneg hΓo hΓ hf hf' hSΓ fun k ↦ eigenvalue_mono hS hT hn hST k

/-- **Strict monotonicity of spectral functions.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let
`f` be differentiable on `Γ` with positive partial derivatives there. If `S ≤ T` in the Loewner
order, `S ≠ T` and `λ(S) ∈ Γ`, then `f(λ(S)) < f(λ(T))`. -/
theorem apply_eigenvalues_lt_of_re_inner_le_of_ne (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (hST : ∀ x, RCLike.re ⟪S x, x⟫_𝕜 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hne : S ≠ T) (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hf' : ∀ μ ∈ Γ, ∀ i, 0 < fderiv ℝ f μ (Pi.single i 1)) (hSΓ : hS.eigenvalues hn ∈ Γ) :
    f (hS.eigenvalues hn) < f (hT.eigenvalues hn) :=
  lt_of_le_of_ne_of_forall_fderiv_single_pos hΓo hΓ hf hf' hSΓ
    (fun k ↦ eigenvalue_mono hS hT hn hST k)
    fun heq ↦ hne (eq_of_re_inner_le_of_eigenvalues_eq hS hT hn hST heq)

end LinearMap.IsSymmetric
