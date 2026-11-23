/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Monotonicity of spectral domains and spectral functions

Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, where `Γ_n` is the open positive orthant: adding a vector
with positive coordinates to a point of `Γ` stays in `Γ`. Then `Γ` is upward closed for the
componentwise order. If `f` is differentiable on `Γ` with nonnegative partial derivatives
`∂_i f`, then `f` is monotone on `Γ`, and strictly monotone if the partial derivatives are
positive: along the segment from `μ ≤ ν` the derivative of `f` is `Σ_i (ν - μ)_i ∂_i f ≥ 0`.

For symmetric operators `S ≤ T` in the Loewner order on a finite-dimensional inner product space,
the decreasingly sorted eigenvalue vectors satisfy `λ(S) ≤ λ(T)` componentwise
(`LinearMap.IsSymmetric.eigenvalue_mono`). So the spectral domain `{T | λ(T) ∈ Γ}` is upward
closed, the spectral function `T ↦ f(λ(T))` is monotone, and it is strictly monotone when the
partial derivatives of `f` are positive: if `λ(S) = λ(T)`, then `T - S ≥ 0` has trace zero, so
`S = T`.

Convexity of `Γ` is not used, and `Γ` need not be symmetric for these statements.

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

variable {n : ℕ} {Γ : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {μ ν : Fin n → ℝ}

/-- **Upward closure.** If `Γ ⊆ ℝⁿ` is open and adding a vector with positive coordinates to a
point of `Γ` stays in `Γ`, then `Γ` is upward closed for the componentwise order. -/
theorem mem_of_le_of_forall_add_mem (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hμ : μ ∈ Γ) (hle : μ ≤ ν) :
    ν ∈ Γ := by
  -- Move down from `μ` by a small multiple of `(1, …, 1)`, staying in `Γ`, and then up to `ν`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΓo μ hμ
  have hmem : μ - (fun _ ↦ ε / 2) ∈ Γ := by
    refine hball (mem_ball_iff_norm.mpr ?_)
    rw [sub_sub_cancel_left, norm_neg]
    refine (pi_norm_const_le (ε / 2)).trans_lt ?_
    rw [Real.norm_of_nonneg (by positivity)]
    linarith
  have h := hΓ _ hmem (ν - μ + (fun _ ↦ ε / 2)) fun i ↦ by
    have := hle i
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith
  rwa [sub_add_add_cancel, add_sub_cancel] at h

/-- The derivative of `f` in a direction `d` is `Σ_i d_i ∂_i f`. -/
private theorem fderiv_apply_eq_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) (d : Fin n → ℝ) :
    L d = ∑ i, d i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- Along the segment from `μ` to `ν ≥ μ`, the function `t ↦ f (μ + t • (ν - μ))` has derivative
`fderiv ℝ f (μ + t • (ν - μ)) (ν - μ)` for `0 ≤ t`. -/
private theorem hasDerivAt_segment (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hμ : μ ∈ Γ) (hle : μ ≤ ν) {t : ℝ} (ht : 0 ≤ t) :
    μ + t • (ν - μ) ∈ Γ ∧ HasDerivAt (fun s : ℝ ↦ f (μ + s • (ν - μ)))
      (fderiv ℝ f (μ + t • (ν - μ)) (ν - μ)) t := by
  have hmem : μ + t • (ν - μ) ∈ Γ := mem_of_le_of_forall_add_mem hΓo hΓ hμ fun i ↦ by
    have := hle i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith
  refine ⟨hmem, ?_⟩
  have hline : HasDerivAt (fun s : ℝ ↦ μ + s • (ν - μ)) (ν - μ) t := by
    simpa using ((hasDerivAt_id t).smul_const (ν - μ)).const_add μ
  exact HasFDerivAt.comp_hasDerivAt t
    ((hf _ hmem).differentiableAt (hΓo.mem_nhds hmem)).hasFDerivAt hline

/-- **Monotonicity of `f`.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let `f` be
differentiable on `Γ` with nonnegative partial derivatives there. Then `f μ ≤ f ν` whenever
`μ ∈ Γ` and `μ ≤ ν`. -/
theorem le_of_le_of_forall_fderiv_single_nonneg (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hf' : ∀ μ ∈ Γ, ∀ i, 0 ≤ fderiv ℝ f μ (Pi.single i 1)) (hμ : μ ∈ Γ) (hle : μ ≤ ν) :
    f μ ≤ f ν := by
  have hd := fun t (ht : t ∈ Icc (0 : ℝ) 1) ↦ hasDerivAt_segment hΓo hΓ hf hμ hle ht.1
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (fun t ht ↦ (hd t ht).2.continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).2.hasDerivWithinAt) fun t ht ↦ by
      rw [fderiv_apply_eq_sum]
      exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (sub_nonneg.mpr (hle i))
        (hf' _ (hd t (interior_subset ht)).1 i)
  simpa using hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one

/-- **Strict monotonicity of `f`.** Let `Γ ⊆ ℝⁿ` be open with `Γ + Γ_n ⊆ Γ`, and let `f` be
differentiable on `Γ` with positive partial derivatives there. Then `f μ < f ν` whenever `μ ∈ Γ`,
`μ ≤ ν` and `μ ≠ ν`. -/
theorem lt_of_le_of_ne_of_forall_fderiv_single_pos (hΓo : IsOpen Γ)
    (hΓ : ∀ μ ∈ Γ, ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → μ + d ∈ Γ) (hf : DifferentiableOn ℝ f Γ)
    (hf' : ∀ μ ∈ Γ, ∀ i, 0 < fderiv ℝ f μ (Pi.single i 1)) (hμ : μ ∈ Γ) (hle : μ ≤ ν)
    (hne : μ ≠ ν) : f μ < f ν := by
  obtain ⟨j, hj⟩ : ∃ j, μ j ≠ ν j := Function.ne_iff.mp hne
  have hd := fun t (ht : t ∈ Icc (0 : ℝ) 1) ↦ hasDerivAt_segment hΓo hΓ hf hμ hle ht.1
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) 1)
    (fun t ht ↦ (hd t ht).2.continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).2.hasDerivWithinAt) fun t ht ↦ by
      have hmem := (hd t (interior_subset ht)).1
      rw [fderiv_apply_eq_sum]
      exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (sub_nonneg.mpr (hle i)) (hf' _ hmem i).le)
        ⟨j, Finset.mem_univ _, mul_pos (sub_pos.mpr ((hle j).lt_of_ne hj)) (hf' _ hmem j)⟩
  simpa using hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one

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

/-- Two symmetric operators `S ≤ T` in the Loewner order with the same eigenvalues are equal: the
operator `T - S` is positive with trace zero. -/
theorem eq_of_re_inner_le_of_eigenvalues_eq (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (hST : ∀ x, RCLike.re ⟪S x, x⟫_𝕜 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (heq : hS.eigenvalues hn = hT.eigenvalues hn) : S = T := by
  have hpos : (T - S).IsPositive := ⟨hT.sub hS, fun x ↦ by
    simpa [inner_sub_left, sub_nonneg] using hST x⟩
  have hsum : ∑ i, hpos.isSymmetric.eigenvalues hn i = 0 := by
    rw [← hpos.isSymmetric.re_trace_eq_sum_eigenvalues hn, map_sub, map_sub,
      hT.re_trace_eq_sum_eigenvalues hn, hS.re_trace_eq_sum_eigenvalues hn, heq, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hpos.nonneg_eigenvalues hn i).mp hsum
  have hTS : T - S = 0 := (hpos.isSymmetric.eigenvectorBasis hn).toBasis.ext fun i ↦ by
    rw [OrthonormalBasis.coe_toBasis, hpos.isSymmetric.apply_eigenvectorBasis,
      hzero i (Finset.mem_univ _), RCLike.ofReal_zero, zero_smul, LinearMap.zero_apply]
  exact (sub_eq_zero.mp hTS).symm

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
