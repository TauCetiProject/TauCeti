/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Overlap

/-!
# Aligned orthonormal families and the orthogonal Procrustes bound

Two orthonormal families `u, v : ι → E` with `d` members span subspaces `U` and `V` whose relative
position is measured by the principal cosines `cos θ₀ ≥ ⋯ ≥ cos θ_{d-1}`, the singular values of the
overlap operator `O = (⟪uᵢ, vⱼ⟫)ᵢⱼ`. The family `v` itself can be badly matched to `u` even when
`U = V`: replacing `v` by another orthonormal basis of `V` changes `∑ⱼ ‖vⱼ - uⱼ‖²` but not the
principal angles. This file chooses the best basis of `V`.

For orthonormal families, `∑ⱼ ‖wⱼ - uⱼ‖² = 2 (d - re ∑ⱼ ⟪uⱼ, wⱼ⟫)`, so making `w` close to `u` means
maximizing `re ∑ⱼ ⟪uⱼ, wⱼ⟫`. Writing an orthonormal family of `V` as `wⱼ = ∑ᵢ Qᵢⱼ vᵢ` for a unitary
coefficient matrix `Q`, this sum is `tr (O Q)`, which is at most `∑ₖ cos θₖ` by Ky Fan's maximum
principle, with equality for a suitable `Q` (the unitary factor of a polar decomposition of `O`).
The resulting *aligned family* spans `V` and satisfies

  `∑ⱼ ‖wⱼ - uⱼ‖² = 2 ∑ₖ (1 - cos θₖ) ≤ 2 ∑ₖ (1 - cos² θₖ) = 2 sin²_F Θ`,

and no orthonormal family in `V` comes closer to `u`. This is the orthogonal Procrustes problem.
The bound converts estimates on the distance between subspaces, such as the Davis–Kahan and
Yu–Wang–Samworth `sin Θ` theorems, into estimates for matched orthonormal bases.

## Main results

* `Orthonormal.sum_norm_sub_sq_eq`: `∑ⱼ ‖wⱼ - uⱼ‖² = 2 (d - re ∑ⱼ ⟪uⱼ, wⱼ⟫)` for orthonormal
  families with `d` members.
* `TauCeti.exists_orthonormal_span_eq_sum_inner_eq`: an orthonormal family `w` spanning the same
  subspace as `v` with `∑ⱼ ⟪uⱼ, wⱼ⟫ = ∑ₖ cos θₖ`.
* `TauCeti.exists_orthonormal_span_eq_sum_norm_sub_sq_le`: the **Procrustes bound**, an orthonormal
  family `w` spanning the same subspace as `v` with `∑ⱼ ‖wⱼ - uⱼ‖² ≤ 2 sin²_F Θ`.
* `TauCeti.two_mul_sum_one_sub_cosPrincipalAngles_le_sum_norm_sub_sq`: optimality, every
  orthonormal family `w` in the span of `v` has `2 ∑ₖ (1 - cos θₖ) ≤ ∑ⱼ ‖wⱼ - uⱼ‖²`.

## References

* P. H. Schönemann, *A generalized solution of the orthogonal Procrustes problem*,
  Psychometrika 31 (1966), 1–10.
* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis–Kahan theorem for
  statisticians*, Biometrika 102 (2015), 315–323.
-/

public section

open Module (finrank)
open Submodule (span)
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- For orthonormal families `u` and `w` with `d` members,
`∑ⱼ ‖wⱼ - uⱼ‖² = 2 (d - re ∑ⱼ ⟪uⱼ, wⱼ⟫)`. -/
theorem Orthonormal.sum_norm_sub_sq_eq {u w : ι → E} (hu : Orthonormal 𝕜 u)
    (hw : Orthonormal 𝕜 w) :
    ∑ j, ‖w j - u j‖ ^ 2 = 2 * (Fintype.card ι - RCLike.re (∑ j, ⟪u j, w j⟫_𝕜)) := by
  have h (j : ι) : ‖w j - u j‖ ^ 2 = 2 - 2 * RCLike.re ⟪u j, w j⟫_𝕜 := by
    rw [@norm_sub_sq 𝕜, hw.1 j, hu.1 j, inner_re_symm]
    ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, map_sum]
  simp [mul_sub, mul_comm]

namespace TauCeti

/-- Pairing `uⱼ` with the image `∑ᵢ aᵢ vᵢ` of a coefficient vector `a` under the coordinate
isometry of `v` gives the `j`-th coordinate of the overlap operator at `a`:
`⟪uⱼ, ∑ᵢ aᵢ vᵢ⟫ = ⟪eⱼ, O a⟫`. -/
private theorem inner_synthesisMapIsometry_eq_inner_overlapOperator (u : ι → E) {v : ι → E}
    (hv : Orthonormal 𝕜 v) (a : EuclideanSpace 𝕜 ι) (j : ι) :
    ⟪u j, hv.synthesisMapIsometry a⟫_𝕜 =
      ⟪EuclideanSpace.basisFun ι 𝕜 j, overlapOperator 𝕜 u v a⟫_𝕜 := by
  rw [EuclideanSpace.basisFun_inner, overlapOperator_def, LinearMap.comp_apply,
    analysisMap_apply, ← hv.synthesisMapIsometry_toLinearMap, LinearIsometry.coe_toLinearMap]

/-- **Aligned orthonormal family.** For orthonormal families `u` and `v` with `d` members, some
orthonormal family `w` spans the same subspace as `v` and satisfies
`∑ⱼ ⟪uⱼ, wⱼ⟫ = cos θ₀ + ⋯ + cos θ_{d-1}`, the sum of the principal cosines of `u` and `v`. By
`TauCeti.two_mul_sum_one_sub_cosPrincipalAngles_le_sum_norm_sub_sq`, no orthonormal family in the
span of `v` is closer to `u`. -/
theorem exists_orthonormal_span_eq_sum_inner_eq {u v : ι → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∃ w : ι → E, Orthonormal 𝕜 w ∧ span 𝕜 (Set.range w) = span 𝕜 (Set.range v) ∧
      ∑ j, ⟪u j, w j⟫_𝕜 =
        ((∑ k ∈ Finset.range (Fintype.card ι), cosPrincipalAngles hu hv k : ℝ) : 𝕜) := by
  obtain ⟨Q, hQ⟩ := (overlapOperator 𝕜 u v).exists_linearIsometryEquiv_trace_comp_eq_kyFanSum
  let e := EuclideanSpace.basisFun ι 𝕜
  let w : ι → E := fun j ↦ hv.synthesisMapIsometry (Q (e j))
  have hw : Orthonormal 𝕜 w :=
    e.orthonormal.comp_linearIsometry (hv.synthesisMapIsometry.comp Q.toLinearIsometry)
  refine ⟨w, hw, ?_, ?_⟩
  · -- `w` lies in the span of `v`, and both spans have dimension `d`.
    have hle : span 𝕜 (Set.range w) ≤ span 𝕜 (Set.range v) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      simp only [w, SetLike.mem_coe, Orthonormal.synthesisMapIsometry_apply]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
    exact Submodule.eq_of_le_of_finrank_eq hle <| by
      rw [finrank_span_eq_card hw.linearIndependent, finrank_span_eq_card hv.linearIndependent]
  · rw [finrank_euclideanSpace, ← sum_range_cosPrincipalAngles_eq_kyFanSum hu hv,
      LinearMap.trace_eq_sum_inner _ e] at hQ
    rw [← hQ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [w, e, inner_synthesisMapIsometry_eq_inner_overlapOperator u hv]
    simp

/-- **Procrustes bound.** For orthonormal families `u` and `v` with the same index type, some
orthonormal family `w` spans the same subspace as `v` and satisfies
`∑ⱼ ‖wⱼ - uⱼ‖² ≤ 2 sin²_F Θ`, twice the squared Frobenius sine between the two spans. -/
theorem exists_orthonormal_span_eq_sum_norm_sub_sq_le {u v : ι → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∃ w : ι → E, Orthonormal 𝕜 w ∧ span 𝕜 (Set.range w) = span 𝕜 (Set.range v) ∧
      ∑ j, ‖w j - u j‖ ^ 2 ≤ 2 * sinThetaSq hu hv := by
  obtain ⟨w, hw, hspan, hsum⟩ := exists_orthonormal_span_eq_sum_inner_eq hu hv
  refine ⟨w, hw, hspan, ?_⟩
  -- `∑ⱼ ‖wⱼ - uⱼ‖² = 2 (d - ∑ₖ cos θₖ)`, and `cos² θₖ ≤ cos θₖ` since `0 ≤ cos θₖ ≤ 1`.
  rw [hu.sum_norm_sub_sq_eq hw, hsum, RCLike.ofReal_re, sinThetaSq_eq_card_sub_sum_sq]
  gcongr with k
  rw [sq]
  exact mul_le_of_le_one_left (cosPrincipalAngles_nonneg hu hv k)
    (cosPrincipalAngles_le_one hu hv k)

/-- **Optimality of the aligned family.** Every orthonormal family `w` in the span of `v` satisfies
`2 ∑ₖ (1 - cos θₖ) ≤ ∑ⱼ ‖wⱼ - uⱼ‖²`; the family of `TauCeti.exists_orthonormal_span_eq_sum_inner_eq`
attains this bound. -/
theorem two_mul_sum_one_sub_cosPrincipalAngles_le_sum_norm_sub_sq {u v w : ι → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) (hw : Orthonormal 𝕜 w)
    (hwv : ∀ j, w j ∈ span 𝕜 (Set.range v)) :
    2 * ∑ k ∈ Finset.range (Fintype.card ι), (1 - cosPrincipalAngles hu hv k) ≤
      ∑ j, ‖w j - u j‖ ^ 2 := by
  -- Write `wⱼ = ∑ᵢ (cⱼ)ᵢ vᵢ`; the coefficient vectors `cⱼ` are orthonormal since synthesis by `v`
  -- is an isometry, so Ky Fan's maximum principle bounds `∑ⱼ ⟪eⱼ, O cⱼ⟫`.
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun 𝕜).mp (hwv j)
  let c' : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 (c j)
  have hwc (j : ι) : hv.synthesisMapIsometry (c' j) = w j := by
    simp [c', hc]
  have hc' : Orthonormal 𝕜 c' :=
    hv.synthesisMapIsometry.orthonormal_comp_iff.mp (by simpa [Function.comp_def, hwc] using hw)
  have hle := (overlapOperator 𝕜 u v).norm_sum_inner_le_kyFanSum
    (EuclideanSpace.basisFun ι 𝕜).orthonormal hc'
  rw [← sum_range_cosPrincipalAngles_eq_kyFanSum hu hv] at hle
  have hsum : ∑ j, ⟪u j, w j⟫_𝕜 =
      ∑ j, ⟪EuclideanSpace.basisFun ι 𝕜 j, overlapOperator 𝕜 u v (c' j)⟫_𝕜 := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← inner_synthesisMapIsometry_eq_inner_overlapOperator u hv, hwc j]
  rw [hu.sum_norm_sub_sq_eq hw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_one]
  gcongr
  exact (RCLike.re_le_norm _).trans (hsum ▸ hle)

end TauCeti
