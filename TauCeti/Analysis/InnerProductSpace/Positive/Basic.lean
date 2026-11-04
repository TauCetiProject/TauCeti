/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Elementary inequalities for positive operators

For a positive operator `T` on a possibly infinite-dimensional Hilbert space, `1 + T` is
invertible (`ContinuousLinearMap.IsPositive.isUnit_one_add`), because
`re ⟪(1 + T) x, x⟫ ≥ ‖x‖²` bounds it below. This applies in particular to `T = X†X`, which makes
`(1 + X†X)⁻¹` available in formulas such as the orthogonal projection onto a graph subspace.

The quadratic form of a positive endomorphism `A` controls its off-diagonal entries,
`2 re ⟪x, A y⟫ ≤ re ⟪x, A x⟫ + re ⟪y, A y⟫`
(`LinearMap.IsPositive.two_mul_re_inner_le`), and on a finite-dimensional space the diagonal
entries along any orthonormal family sum to at most the trace
(`LinearMap.IsPositive.sum_re_inner_le_re_trace`). These are the inputs to Ky Fan's maximum
principle for positive operators.
-/

public section

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a positive endomorphism `A`, `2 re ⟪x, A y⟫ ≤ re ⟪x, A x⟫ + re ⟪y, A y⟫`. -/
theorem IsPositive.two_mul_re_inner_le {A : E →ₗ[𝕜] E} (hA : A.IsPositive) (x y : E) :
    2 * RCLike.re ⟪x, A y⟫_𝕜 ≤ RCLike.re ⟪x, A x⟫_𝕜 + RCLike.re ⟪y, A y⟫_𝕜 := by
  have h := hA.re_inner_nonneg_right (x - y)
  have hsymm : RCLike.re ⟪y, A x⟫_𝕜 = RCLike.re ⟪x, A y⟫_𝕜 := by
    rw [← hA.isSymmetric x y, ← inner_conj_symm, RCLike.conj_re]
  simp only [map_sub, inner_sub_left, inner_sub_right] at h
  linarith

/-- For a positive endomorphism `A` of a finite-dimensional space, the diagonal entries of `A` along
an orthonormal family have real parts summing to at most the real part of the trace. -/
theorem IsPositive.sum_re_inner_le_re_trace [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsPositive) {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) :
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
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦ hA.re_inner_nonneg_right x
    _ = ∑ x : u, RCLike.re ⟪(x : E), A x⟫_𝕜 := (Finset.sum_coe_sort u _).symm

end LinearMap

namespace ContinuousLinearMap

open scoped InnerProductSpace InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- On a complete space, `1 + T` is invertible for every positive operator `T`, since
`re ⟪(1 + T) x, x⟫ = ‖x‖² + re ⟪T x, x⟫ ≥ ‖x‖²`. For instance `1 + X†X` is invertible, by
`ContinuousLinearMap.isPositive_adjoint_comp_self`. -/
theorem IsPositive.isUnit_one_add {T : E →L[𝕜] E} (hT : T.IsPositive) : IsUnit (1 + T) := by
  refine isUnit_of_forall_le_norm_inner_map _ one_pos fun x => ?_
  rw [NNReal.coe_one, mul_one]
  calc ‖x‖ ^ 2 ≤ RCLike.re ⟪(1 + T) x, x⟫_𝕜 := by
        rw [add_apply, one_apply_eq_self, inner_add_left, map_add, inner_self_eq_norm_sq]
        exact le_add_of_nonneg_right (hT.re_inner_nonneg_left x)
    _ ≤ ‖⟪(1 + T) x, x⟫_𝕜‖ := RCLike.re_le_norm _

end ContinuousLinearMap
