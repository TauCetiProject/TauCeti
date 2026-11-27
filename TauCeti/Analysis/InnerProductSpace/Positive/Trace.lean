/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.OpNorm
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Trace bounds for nonnegative quadratic forms

In finite dimension, the real parts of the diagonal entries of an endomorphism along an
orthonormal family sum to at most the real part of its trace, provided the real part of its
quadratic form is nonnegative. Symmetry is not required. The real part of the quadratic form
is bounded by the real part of the trace times the squared vector norm. For a positive
endomorphism, which also satisfies symmetry, the operator norm is at most the real part of the
trace.

Nonnegativity of the real part of the trace also holds without finite dimension, since the
algebraic trace is totalized as zero there.
-/

public section

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For an endomorphism with nonnegative real part of its quadratic form on a finite-dimensional
space, the real parts of the diagonal entries along an orthonormal family sum to at most the
real part of its trace.
Symmetry is not required. -/
theorem sum_re_inner_le_re_trace_of_re_inner_nonneg [FiniteDimensional 𝕜 E]
    (A : E →ₗ[𝕜] E) (hA : ∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_𝕜)
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    ∑ i, RCLike.re ⟪v i, A (v i)⟫_𝕜 ≤ RCLike.re (A.trace 𝕜 E) := by
  classical
  obtain ⟨u, b, hvu, hb⟩ :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
      |>.exists_orthonormalBasis_extension
  rw [trace_eq_sum_inner A b, map_sum, hb]
  have hsub : Finset.univ.image v ⊆ u := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hvu ⟨i, rfl⟩
  calc ∑ i, RCLike.re ⟪v i, A (v i)⟫_𝕜
      = ∑ x ∈ Finset.univ.image v, RCLike.re ⟪x, A x⟫_𝕜 := by
        rw [Finset.sum_image fun i _ j _ h ↦ hv.linearIndependent.injective h]
    _ ≤ ∑ x ∈ u, RCLike.re ⟪x, A x⟫_𝕜 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦ hA x
    _ = ∑ x : u, RCLike.re ⟪(x : E), A x⟫_𝕜 := (Finset.sum_coe_sort u _).symm

/-- Nonnegativity of the real part of the quadratic form implies that the real part of the trace
is nonnegative, without
assuming symmetry. The algebraic trace is totalized as zero outside finite dimension. -/
theorem re_trace_nonneg_of_re_inner_nonneg (A : E →ₗ[𝕜] E)
    (hA : ∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_𝕜) : 0 ≤ RCLike.re (A.trace 𝕜 E) := by
  classical
  by_cases hfinite : FiniteDimensional 𝕜 E
  · have : FiniteDimensional 𝕜 E := hfinite
    have h := A.sum_re_inner_le_re_trace_of_re_inner_nonneg hA
      (v := fun i : Empty ↦ i.elim)
        (orthonormal_subsingleton_iff.mpr fun i ↦ i.elim)
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using h
  · simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfinite]

/-- For an endomorphism on a finite-dimensional space with nonnegative real part of its quadratic
form, that real part at `x` is bounded by the real part of the trace times `‖x‖²`. Symmetry is
not required. -/
theorem re_inner_le_re_trace_mul_norm_sq [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E)
    (hA : ∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_𝕜) (x : E) :
    RCLike.re ⟪x, A x⟫_𝕜 ≤ RCLike.re (A.trace 𝕜 E) * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  let e : E := (‖x‖⁻¹ : 𝕜) • x
  have he : ‖e‖ = 1 := norm_smul_inv_norm hx
  have hon : Orthonormal 𝕜 (fun _ : Unit ↦ e) :=
    orthonormal_subsingleton_iff.mpr fun _ ↦ he
  have hunit : RCLike.re ⟪e, A e⟫_𝕜 ≤ RCLike.re (A.trace 𝕜 E) := by
    simpa using A.sum_re_inner_le_re_trace_of_re_inner_nonneg hA hon
  have hvec : x = (‖x‖ : 𝕜) • e := by
    simpa only [e, RCLike.ofReal_inv] using
      (smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)) x).symm
  have hinner : RCLike.re ⟪x, A x⟫_𝕜 = ‖x‖ ^ 2 * RCLike.re ⟪e, A e⟫_𝕜 := by
    have hscale := A.toContinuousLinearMap.reApplyInnerSelf_smul e (c := (‖x‖ : 𝕜))
    simpa only [← hvec, ContinuousLinearMap.reApplyInnerSelf_apply,
      LinearMap.coe_toContinuousLinearMap', RCLike.norm_ofReal, abs_norm,
      inner_re_symm] using hscale
  rw [hinner]
  nlinarith [mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖x‖)]

/-- The operator norm of a positive endomorphism of a finite-dimensional inner-product space is
at most the real part of its trace. Positivity includes symmetry and quadratic nonnegativity. -/
theorem IsPositive.norm_toContinuousLinearMap_le_re_trace [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsPositive) :
    ‖A.toContinuousLinearMap‖ ≤ RCLike.re (A.trace 𝕜 E) := by
  have hsym : A.toContinuousLinearMap.IsSymmetric := by
    simpa only [LinearMap.coe_toContinuousLinearMap] using hA.isSymmetric
  refine ContinuousLinearMap.norm_le_of_forall_norm_eq_one_abs_re_inner_map_self_le
    A.toContinuousLinearMap hsym (RCLike.nonneg_iff.mp hA.trace_nonneg).1
    fun x hx ↦ ?_
  have hquad := A.re_inner_le_re_trace_mul_norm_sq hA.re_inner_nonneg_right x
  simp only [LinearMap.coe_toContinuousLinearMap']
  rw [inner_re_symm (A x) x, abs_of_nonneg (hA.re_inner_nonneg_right x)]
  simpa only [hx, one_pow, mul_one] using hquad

end LinearMap
