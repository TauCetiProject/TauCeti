/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distances and the inverse Gram matrix

For a finite linearly independent family, the diagonal of the inverse Gram matrix is the
reciprocal squared distance of each vector from the span of the others. Summing gives a
geometric formula for the trace of the inverse Gram matrix. These formulas are used in the
negative second-moment identity for singular values.

The ambient real or complex inner product space need not be complete or finite-dimensional.

## References

* T. Tao, *Topics in Random Matrix Theory*, Section 2.7, negative second-moment identity.
-/

public section

noncomputable section

open Matrix Submodule
open scoped InnerProductSpace

namespace LinearIndependent

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι] {v : ι → E}

/-- The columns of the inverse Gram matrix give vectors biorthogonal to the original family. -/
@[simp]
theorem inner_sum_smul_gram_inv (hv : LinearIndependent 𝕜 v) (i j : ι) :
    ⟪v j, ∑ k, (gram 𝕜 v)⁻¹ k i • v k⟫_𝕜 = if j = i then 1 else 0 := by
  have h := congr_fun (congr_fun (mul_nonsing_inv (gram 𝕜 v)
    (isUnit_iff_ne_zero.2 (det_gram_ne_zero_iff_linearIndependent.2 hv))) j) i
  simp only [Matrix.mul_apply, Matrix.one_apply, gram_apply] at h
  simpa only [inner_sum, inner_smul_right, mul_comm] using h

/-- The diagonal of the inverse Gram matrix is the reciprocal squared distance from a vector
to the span of the other vectors. -/
theorem gram_inv_apply_self_eq_inv_infDist_sq (hv : LinearIndependent 𝕜 v) (i : ι) :
    (gram 𝕜 v)⁻¹ i i =
      (((Metric.infDist (v i) (span 𝕜 (v '' {i}ᶜ) : Set E)) ^ 2)⁻¹ : ℝ) := by
  let u : E := ∑ k, (gram 𝕜 v)⁻¹ k i • v k
  have hu (j : ι) : ⟪v j, u⟫_𝕜 = if j = i then 1 else 0 :=
    inner_sum_smul_gram_inv hv i j
  have hu' (j : ι) : ⟪u, v j⟫_𝕜 = if j = i then 1 else 0 := by
    rw [← inner_conj_symm u (v j), hu]
    split_ifs <;> simp
  have hnorm : (gram 𝕜 v)⁻¹ i i = (‖u‖ : 𝕜) ^ 2 := by
    calc
      _ = ⟪u, u⟫_𝕜 := by
        conv_rhs => rhs; unfold u
        simp [inner_sum, inner_smul_right, hu']
      _ = _ := inner_self_eq_norm_sq_to_K u
  have hune : u ≠ 0 := by
    intro h
    simpa [h] using hu i
  have hdiag : (gram 𝕜 v)⁻¹ i i ≠ 0 := by
    rw [hnorm]
    exact pow_ne_zero _ (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hune))
  let c : 𝕜 := ((gram 𝕜 v)⁻¹ i i)⁻¹
  let K := span 𝕜 (v '' {i}ᶜ)
  have hmem : v i - c • u ∈ K := by
    have heq : v i - c • u =
        ∑ j, ((if j = i then 1 else 0) - c * (gram 𝕜 v)⁻¹ j i) • v j := by
      simp [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum, u]
    rw [heq]
    apply K.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j
      simp [c, inv_mul_cancel₀ hdiag]
    · exact K.smul_mem _ (subset_span ⟨j, hji, rfl⟩)
  have horth : ∀ z ∈ K, ⟪u, z⟫_𝕜 = 0 := by
    intro z hz
    refine span_induction (fun y hy ↦ ?_) (by simp)
      (fun x y _ _ hx hy ↦ by simp [inner_add_right, hx, hy])
      (fun a x _ hx ↦ by simp [inner_smul_right, hx]) hz
    obtain ⟨j, hj, rfl⟩ := hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    simpa only [hu', ite_eq_right_iff, one_ne_zero, imp_false] using hj
  have hdist : Metric.infDist (v i) (K : Set E) = ‖c • u‖ := by
    rw [Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    have hmin := K.norm_eq_iInf_iff_inner_eq_zero (u := v i) hmem
    convert (hmin.2 fun z hz ↦ by simp [inner_smul_left, horth z hz]).symm using 1
    simp only [sub_sub_cancel]
  rw [hdist, norm_smul, mul_pow, norm_inv, hnorm, norm_pow,
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  push_cast
  field_simp

/-- The real trace of the inverse Gram matrix is the sum of reciprocal squared distances to
the spans of the other vectors. The empty family gives zero on both sides. -/
theorem re_trace_gram_inv_eq_sum_inv_infDist_sq (hv : LinearIndependent 𝕜 v) :
    RCLike.re (gram 𝕜 v)⁻¹.trace =
      ∑ i, ((Metric.infDist (v i) (span 𝕜 (v '' {i}ᶜ) : Set E)) ^ 2)⁻¹ := by
  simp only [trace, diag, gram_inv_apply_self_eq_inv_infDist_sq hv, map_sum,
    RCLike.ofReal_re]

end LinearIndependent
