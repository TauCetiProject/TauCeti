/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Isometry
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Pythagoras

/-!
# Near isometries and the Hilbert–Schmidt defect

Let `A : S →L[𝕜] T` be a linear map out of a finite-dimensional inner product space. An isometry
satisfies `‖A ∘ pr_U‖_HS² = dim U` for every subspace `U ≤ S`, where `pr_U` is the orthogonal
projection onto `U` and `‖·‖_HS` the Hilbert–Schmidt norm. We call `A` a **near isometry with
error `ε`** if `‖A ∘ pr_U‖_HS² ≥ dim U - ε · dim S` for every subspace `U`.

The Hilbert–Schmidt size of the defect `A† A - 1` controls this error. For a unit vector `f`,
`‖A f‖² = 1 + re ⟪f, (A† A - 1) f⟫ ≥ 1 - ‖(A† A - 1) f‖`; summing over an orthonormal basis of `U`
and applying Cauchy–Schwarz to the sum
(`ContinuousLinearMap.sum_norm_apply_le_sqrt_card_mul_hilbertSchmidtNorm`) gives
`‖A ∘ pr_U‖_HS² ≥ dim U - √(dim U) · ‖A† A - 1‖_HS`. Hence `‖A† A - 1‖_HS² ≤ ε² dim S` with
`ε ≥ 0` makes `A` a near isometry with error `ε`.

Following a near isometry by an orthogonal projection `p` of the target costs at most the
normalised energy `‖(1 - p) A‖_HS² / dim S` that `p` removes, by Pythagoras for the
Hilbert–Schmidt norm (`ContinuousLinearMap.sq_hilbertSchmidtNorm_eq_comp_add_one_sub_comp`). The
energy removed by a product `p q` is bounded in the same file
(`ContinuousLinearMap.sq_hilbertSchmidtNorm_one_sub_mul_comp_le`).

## Main definitions

* `ContinuousLinearMap.IsNearIsometry A ε`: `A` is a near isometry with error `ε`.

## Main results

* `ContinuousLinearMap.isNearIsometry_of_one_le` and
  `ContinuousLinearMap.isNearIsometry_zero_of_isometry`: every map is a near isometry with error
  `ε ≥ 1`, and an isometry is one with error `0`.
* `ContinuousLinearMap.finrank_sub_sqrt_mul_le_sq_hilbertSchmidtNorm_comp_starProjection`:
  `dim U - √(dim U) · ‖A† A - 1‖_HS ≤ ‖A ∘ pr_U‖_HS²`.
* `ContinuousLinearMap.finrank_sub_mul_sqrt_le_sq_hilbertSchmidtNorm_comp_starProjection` and
  `ContinuousLinearMap.isNearIsometry_of_sq_hilbertSchmidtNorm_le`: if
  `‖A† A - 1‖_HS² ≤ ε² dim S` with `ε ≥ 0`, then `‖A ∘ pr_U‖_HS² ≥ dim U - ε √(dim U · dim S)`
  for every `U`, so `A` is a near isometry with error `ε`.
* `ContinuousLinearMap.IsNearIsometry.isStarProjection_comp`: if `A` is a near isometry with error
  `ε`, `p` is an orthogonal projection and `‖(1 - p) A‖_HS² ≤ δ dim S`, then `p A` is a near
  isometry with error `ε + δ`.

## References

* L. R. Welch, *Lower bounds on the maximum cross correlation of signals*, IEEE Transactions on
  Information Theory 20 (1974), 397–399.
* The statements follow the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `New/Spanning/SecondMoment/FewTranslates.lean`
  (`New.hilbertSchmidtNorm`, `New.IsNearIsometry`, `New.isNearIsometry_of_hilbertSchmidtNorm_le`,
  `New.IsNearIsometry.proj_comp`).
-/

public section

open scoped InnerProductSpace
open Module RCLike

namespace ContinuousLinearMap

variable {𝕜 S T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S] [CompleteSpace S]
  [NormedAddCommGroup T] [InnerProductSpace 𝕜 T]

/-- A linear map `A : S →L[𝕜] T` out of a finite-dimensional inner product space is a **near
isometry with error `ε`** if `‖A ∘ pr_U‖_HS² ≥ dim U - ε · dim S` for every subspace `U` of `S`,
where `pr_U` is the orthogonal projection onto `U` and `‖·‖_HS` is the Hilbert–Schmidt norm
`ContinuousLinearMap.hilbertSchmidtNorm`. -/
def IsNearIsometry (A : S →L[𝕜] T) (ε : ℝ) : Prop :=
  ∀ U : Submodule 𝕜 S,
    (finrank 𝕜 U : ℝ) - ε * finrank 𝕜 S ≤ (A ∘L U.starProjection).hilbertSchmidtNorm ^ 2

/-- Unfolding lemma for `ContinuousLinearMap.IsNearIsometry`. -/
theorem isNearIsometry_iff (A : S →L[𝕜] T) (ε : ℝ) :
    A.IsNearIsometry ε ↔ ∀ U : Submodule 𝕜 S,
      (finrank 𝕜 U : ℝ) - ε * finrank 𝕜 S ≤ (A ∘L U.starProjection).hilbertSchmidtNorm ^ 2 :=
  Iff.rfl

/-- A near isometry with error `ε` is one with every larger error. -/
theorem IsNearIsometry.mono {A : S →L[𝕜] T} {ε ε' : ℝ} (hA : A.IsNearIsometry ε)
    (hε : ε ≤ ε') : A.IsNearIsometry ε' := fun U ↦ by
  have : ε * finrank 𝕜 S ≤ ε' * finrank 𝕜 S := by gcongr
  linarith [hA U]

/-- Every linear map is a near isometry with error `ε ≥ 1`, since `dim U ≤ dim S`. -/
theorem isNearIsometry_of_one_le (A : S →L[𝕜] T) {ε : ℝ} (hε : 1 ≤ ε) :
    A.IsNearIsometry ε := fun U ↦ by
  have hU : (finrank 𝕜 U : ℝ) ≤ finrank 𝕜 S := by exact_mod_cast U.finrank_le
  have : (finrank 𝕜 S : ℝ) ≤ ε * finrank 𝕜 S := le_mul_of_one_le_left (Nat.cast_nonneg _) hε
  linarith [sq_nonneg (A ∘L U.starProjection).hilbertSchmidtNorm]

/-- An isometry is a near isometry with error `0`: it has `‖A ∘ pr_U‖_HS² = dim U`. -/
theorem isNearIsometry_zero_of_isometry {A : S →L[𝕜] T} (hA : Isometry A) :
    A.IsNearIsometry 0 := fun U ↦ by
  rw [zero_mul, sub_zero, hilbertSchmidtNorm_comp_starProjection,
    sq_hilbertSchmidtNorm_eq_sum _ (stdOrthonormalBasis 𝕜 U)]
  simp [(AddMonoidHomClass.isometry_iff_norm A).mp hA, Submodule.norm_coe,
    OrthonormalBasis.norm_eq_one]

section Defect

variable [CompleteSpace T]

omit [FiniteDimensional 𝕜 S] in
/-- For a unit vector `f`, `‖A f‖² ≥ 1 - ‖(A† A - 1) f‖`. -/
private theorem one_sub_norm_le_norm_sq (A : S →L[𝕜] T) {f : S} (hf : ‖f‖ = 1) :
    1 - ‖(adjoint A ∘L A - 1) f‖ ≤ ‖A f‖ ^ 2 := by
  have h : ‖A f‖ ^ 2 = 1 + re ⟪f, (adjoint A ∘L A - 1) f⟫_𝕜 := by
    rw [apply_norm_sq_eq_inner_adjoint_right, sub_apply, one_apply_eq_self, inner_sub_right,
      map_sub, inner_self_eq_norm_sq, hf]
    ring
  have h' : |re ⟪f, (adjoint A ∘L A - 1) f⟫_𝕜| ≤ ‖(adjoint A ∘L A - 1) f‖ := by
    simpa [hf] using (abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := 𝕜) f _)
  rw [h]
  linarith [neg_abs_le (re ⟪f, (adjoint A ∘L A - 1) f⟫_𝕜)]

/-- **The Hilbert–Schmidt defect bounds the loss on every subspace.** For every subspace `U`,
`dim U - √(dim U) · ‖A† A - 1‖_HS ≤ ‖A ∘ pr_U‖_HS²`. -/
theorem finrank_sub_sqrt_mul_le_sq_hilbertSchmidtNorm_comp_starProjection (A : S →L[𝕜] T)
    (U : Submodule 𝕜 S) :
    (finrank 𝕜 U : ℝ) - √(finrank 𝕜 U) * (adjoint A ∘L A - 1).hilbertSchmidtNorm ≤
      (A ∘L U.starProjection).hilbertSchmidtNorm ^ 2 := by
  set b := stdOrthonormalBasis 𝕜 U
  have hsum : (A ∘L U.starProjection).hilbertSchmidtNorm ^ 2 = ∑ j, ‖A (b j)‖ ^ 2 := by
    rw [hilbertSchmidtNorm_comp_starProjection, sq_hilbertSchmidtNorm_eq_sum _ b]
    simp only [comp_apply, Submodule.subtypeL_apply]
  have hle : ∑ j, (1 - ‖(adjoint A ∘L A - 1) (b j)‖) ≤ ∑ j, ‖A (b j)‖ ^ 2 :=
    Finset.sum_le_sum fun j _ ↦ one_sub_norm_le_norm_sq A (b.norm_eq_one j)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hle
  -- Cauchy–Schwarz for the columns of the defect on the orthonormal family `(b j)` in `S`.
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 S
  have hcs := sum_norm_apply_le_sqrt_card_mul_hilbertSchmidtNorm (adjoint A ∘L A - 1) c
    (hilbertSchmidtEnergy_ne_top _ c) (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
  simp only [Fintype.card_fin, Function.comp_apply, Submodule.coe_subtypeₗᵢ,
    Submodule.subtype_apply] at hcs
  linarith

/-- If `‖A† A - 1‖_HS² ≤ ε² · dim S` with `ε ≥ 0`, then
`‖A ∘ pr_U‖_HS² ≥ dim U - ε · √(dim U · dim S)` for every subspace `U`. -/
theorem finrank_sub_mul_sqrt_le_sq_hilbertSchmidtNorm_comp_starProjection {A : S →L[𝕜] T}
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : (adjoint A ∘L A - 1).hilbertSchmidtNorm ^ 2 ≤ ε ^ 2 * finrank 𝕜 S)
    (U : Submodule 𝕜 S) :
    (finrank 𝕜 U : ℝ) - ε * √(finrank 𝕜 U * finrank 𝕜 S) ≤
      (A ∘L U.starProjection).hilbertSchmidtNorm ^ 2 := by
  have hX : (adjoint A ∘L A - 1).hilbertSchmidtNorm ≤ ε * √(finrank 𝕜 S) := by
    rw [← Real.sqrt_sq hε, ← Real.sqrt_mul (sq_nonneg ε)]
    exact Real.le_sqrt_of_sq_le h
  have key : √(finrank 𝕜 U) * (adjoint A ∘L A - 1).hilbertSchmidtNorm ≤
      ε * √(finrank 𝕜 U * finrank 𝕜 S) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_left_comm]
    gcongr
  linarith [finrank_sub_sqrt_mul_le_sq_hilbertSchmidtNorm_comp_starProjection A U]

/-- **A small Hilbert–Schmidt defect gives a near isometry.** If `‖A† A - 1‖_HS² ≤ ε² · dim S`
with `ε ≥ 0`, then `A` is a near isometry with error `ε`. -/
theorem isNearIsometry_of_sq_hilbertSchmidtNorm_le {A : S →L[𝕜] T} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (adjoint A ∘L A - 1).hilbertSchmidtNorm ^ 2 ≤ ε ^ 2 * finrank 𝕜 S) :
    A.IsNearIsometry ε := fun U ↦ by
  have hUS : √(finrank 𝕜 U * finrank 𝕜 S : ℝ) ≤ finrank 𝕜 S := by
    refine Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, ?_⟩
    rw [sq]
    gcongr
    exact_mod_cast U.finrank_le
  have : ε * √(finrank 𝕜 U * finrank 𝕜 S : ℝ) ≤ ε * finrank 𝕜 S := by gcongr
  linarith [finrank_sub_mul_sqrt_le_sq_hilbertSchmidtNorm_comp_starProjection hε h U]

end Defect

section Projection

variable [CompleteSpace T]

/-- **Projecting a near isometry.** If `A` is a near isometry with error `ε`, `p` is an orthogonal
projection of the target and `‖(1 - p) A‖_HS² ≤ δ · dim S`, then `p A` is a near isometry with
error `ε + δ`. -/
theorem IsNearIsometry.isStarProjection_comp {A : S →L[𝕜] T} {ε δ : ℝ}
    (hA : A.IsNearIsometry ε) {p : T →L[𝕜] T} (hp : IsStarProjection p)
    (hδ : ((1 - p) ∘L A).hilbertSchmidtNorm ^ 2 ≤ δ * finrank 𝕜 S) :
    (p ∘L A).IsNearIsometry (ε + δ) := fun U ↦ by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 S
  have hpy := sq_hilbertSchmidtNorm_eq_comp_add_one_sub_comp hp (A ∘L U.starProjection) b
    (hilbertSchmidtEnergy_ne_top _ b)
  have hcomp : ((1 - p) ∘L A ∘L U.starProjection).hilbertSchmidtNorm ≤
      ((1 - p) ∘L A).hilbertSchmidtNorm := by
    rw [← comp_assoc]
    refine (hilbertSchmidtNorm_comp_le_right_of_finiteDimensional _ _).trans ?_
    exact mul_le_of_le_one_right (hilbertSchmidtNorm_nonneg _) U.starProjection_norm_le
  have hsq := pow_le_pow_left₀ (hilbertSchmidtNorm_nonneg _) hcomp 2
  rw [comp_assoc]
  linarith [hA U]

end Projection

end ContinuousLinearMap
