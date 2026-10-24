/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.BasisSpan
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.Projection.FrobeniusSine
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The overlap operator of two finite families and their principal cosines

For finite families `u : ι → E` and `v : κ → E` in an inner product space, the *overlap operator*
`TauCeti.overlapOperator` (defined with the frame operators in
`TauCeti.Analysis.InnerProductSpace.Frame`) is analysis by `u` after synthesis by `v`,

`EuclideanSpace 𝕜 κ → EuclideanSpace 𝕜 ι`, `a ↦ (⟪uᵢ, ∑ⱼ aⱼ vⱼ⟫)ᵢ`,

whose matrix in the standard coordinates is `(⟪uᵢ, vⱼ⟫)ᵢⱼ`. When `E` is finite-dimensional it is
`S_u† S_v` for the synthesis maps `S_u`, `S_v`; for orthonormal families these are the coordinate
isometries `Orthonormal.synthesisMapIsometry`, and the overlap operator records the relative
position of the two spanned subspaces in coordinates. On the diagonal it is the Gram operator.

For orthonormal families the singular values of the overlap operator are the *principal cosines*
`cos θ₀ ≥ cos θ₁ ≥ ⋯` of the two spans (Björck–Golub): writing `S_u`, `S_v` for the coordinate
isometries, the cosine map of the spans `U` and `V` is `P_V P_U = S_v (S_v† S_u) S_u†`, and the
outer isometric factors do not change singular values. So these family-level cosines are the
subspace-level `Submodule.principalCosines U V`; for two unit vectors the single principal cosine
of the lines they span is `‖⟪u, v⟫‖`. Defining them as singular values makes
nonnegativity, ordering and symmetry instances of the singular-value API rather than separate
arguments; the bound `cos θₖ ≤ 1` comes from the overlap operator being a contraction. The sum of
their squares is the squared Frobenius norm `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` of the overlap matrix, which gives
the *squared Frobenius sine* `sin²_F Θ = ∑ₖ (1 - cos² θₖ)` of two families of the same size as
`d - ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`. Equivalently, `sin²_F Θ = ∑ⱼ ‖P_{Uᗮ} vⱼ‖²` is the total squared
distance of the `vⱼ` from the span `U` of the `uᵢ`. When the `uᵢ` are the members of an orthonormal
basis `(bₖ)` indexed by a coordinate block `s`, `P_{Uᗮ}` is the projection onto the span of the
complementary block, which gives the cross-block form `sin²_F Θ = ∑ⱼ ∑_{k ∉ s} ‖⟪bₖ, vⱼ⟫‖²`.
For two eigenbases of symmetric operators and a common index block, this expresses the Frobenius
sine between corresponding eigenspaces through the overlaps of eigenvectors across the blocks.

The overlap operator and its Frobenius identity make sense for arbitrary finite families; the
principal cosines and the squared Frobenius sine are defined only for orthonormal families.

## Main declarations

* `TauCeti.norm_overlapOperator_apply_le`: for orthonormal families it is a contraction.
* `TauCeti.sum_sq_singularValues_overlapOperator`: `∑ₖ σₖ² = ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.
* `TauCeti.cosPrincipalAngles`: the principal cosines of two orthonormal families, as singular
  values of the overlap operator, with `cosPrincipalAngles_nonneg`, `cosPrincipalAngles_le_one`,
  `cosPrincipalAngles_antitone` and `cosPrincipalAngles_comm`.
* `Orthonormal.principalCosines_eq_cosPrincipalAngles`: the principal cosines of the spans of two
  orthonormal families are the principal cosines of the families.
* `Submodule.principalCosines_span_singleton`: for unit vectors `u` and `v`, the principal cosines
  of `𝕜 ∙ u` and `𝕜 ∙ v` are `‖⟪u, v⟫‖` followed by zeros.
* `TauCeti.sinThetaSq`: the squared Frobenius sine of two orthonormal families, with
  `TauCeti.sinThetaSq_eq_card_sub_sum_norm_inner_sq` and `TauCeti.sinThetaSq_self`.
* `TauCeti.sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq`: `sin²_F Θ = ∑ⱼ ‖P_{Uᗮ} vⱼ‖²`.
* `Submodule.sq_sinThetaFrobenius_eq_sinThetaSq_of_orthonormal`: for arbitrary
  finite orthonormal families the squared subspace Frobenius sine equals `TauCeti.sinThetaSq`.
* `OrthonormalBasis.sq_sinThetaFrobenius_spanIndices`: the cross-overlap formula for independently
  indexed orthonormal-basis blocks.
* `TauCeti.sinThetaSq_comp_subtypeVal_eq_sum_compl_norm_inner_sq` and
  `TauCeti.sinThetaSq_comp_subtypeVal_comp_subtypeVal_eq_sum_compl_norm_inner_sq`: the cross-block
  form of the squared Frobenius sine for coordinate blocks of orthonormal bases.

## Provenance

The cross-block Frobenius sine identity is adapted from the AIQ-Kitware DKPS
formalization (Kitware, Inc.; Apache-2.0) and the canonical eigenblock bridge.
The remaining overlap identities are TauCeti developments.

## References

* Å. Björck and G. H. Golub, *Numerical methods for computing angles between linear subspaces*,
  Math. Comp. 27 (1973), 579–594.
* G. H. Golub and C. F. Van Loan, *Matrix Computations*, fourth edition, Johns Hopkins University
  Press, 2013, Section 6.4.3.
* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis–Kahan theorem for
  statisticians*, Biometrika 102 (2015), 315–323.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι]

/-- The squared norm of the projection onto the complement of a coordinate block
is the sum of squared inner products with the complementary basis vectors. -/
theorem norm_starProjection_orthogonal_spanIndices_sq [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    ‖(b.spanIndices (↑s : Set ι))ᗮ.starProjection x‖ ^ 2 =
      ∑ k ∈ sᶜ, ‖⟪b k, x⟫_𝕜‖ ^ 2 := by
  have hc : Submodule.span 𝕜
      (Set.range (b ∘ ((↑) : (sᶜ : Finset ι) → ι))) =
        (b.spanIndices (↑s : Set ι))ᗮ := by
    rw [b.orthogonal_spanIndices, ← Finset.coe_compl,
      b.span_range_comp_subtypeVal_eq_spanIndices]
  rw [(b.orthonormal.comp _ Subtype.val_injective).norm_starProjection_sq_eq_sum hc]
  exact Finset.sum_coe_sort sᶜ fun k ↦ ‖⟪b k, x⟫_𝕜‖ ^ 2

/-- For an arbitrary target subspace `U`, the squared Frobenius sine from a
coordinate block of an orthonormal basis `b` to `U` is the total squared
orthogonal projection of the selected vectors onto `Uᗮ`. -/
private theorem sq_sinThetaFrobenius_spanIndices_eq_sum_projection (b : OrthonormalBasis ι 𝕜 E)
    (s : Finset ι) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (b.spanIndices (↑s : Set ι)).sinThetaFrobenius U ^ 2 =
      ∑ j ∈ s, ‖Uᗮ.starProjection (b j)‖ ^ 2 := by
  classical
  set V := b.spanIndices (↑s : Set ι) with hV
  have hb (j : ι) :
      (V.sinThetaMap U) (b j) =
        if j ∈ s then Uᗮ.starProjection (b j) else 0 := by
    by_cases hj : j ∈ s
    · simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_eq_self_iff.mpr (b.mem_spanIndices_of_mem hj)]
    · have horth : b j ∈ Vᗮ := by
        rw [b.orthogonal_spanIndices]
        exact b.mem_spanIndices_of_mem (by simpa using hj)
      simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_apply_eq_zero_iff.mpr horth]
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ j, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          rw [Submodule.sinThetaFrobenius_def]
          exact TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b _
    _ = ∑ j ∈ s, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          exact (Finset.sum_subset (Finset.subset_univ s)
            (by
              intro j _ hj
              rw [hb j]
              simp [hj])).symm
    _ = ∑ j ∈ s, ‖Uᗮ.starProjection (b j)‖ ^ 2 := by
          exact Finset.sum_congr rfl fun j hj ↦ by
            rw [hb j]
            simp [hj]

end OrthonormalBasis

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- For any finite orthonormal family spanning `V`, the squared Frobenius sine
from `V` to `U` is the sum of the squared orthogonal projections of its vectors
onto `Uᗮ`. In particular, the value does not depend on the chosen family. -/
theorem sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection] [U.HasOrthogonalProjection]
    {κ : Type*} [Fintype κ] {v : κ → E} (hv : Orthonormal 𝕜 v)
    (hV : Submodule.span 𝕜 (Set.range v) = V) :
    V.sinThetaFrobenius U ^ 2 = ∑ j, ‖Uᗮ.starProjection (v j)‖ ^ 2 := by
  classical
  have hvinj : Function.Injective v := hv.linearIndependent.injective
  have hvRange : Orthonormal 𝕜 ((↑) : Set.range v → E) :=
    (orthonormal_subtype_range hvinj).mpr hv
  obtain ⟨t, b, hsubset, hb⟩ := hvRange.exists_orthonormalBasis_extension
  let e : κ ↪ t :=
    ⟨fun j => ⟨v j, hsubset (Set.mem_range_self j)⟩,
      fun i j hij => hvinj (congrArg Subtype.val hij)⟩
  set s : Finset t := Finset.univ.image e with hs
  have hbe (j : κ) : b (e j) = v j := by
    calc
      b (e j) = (e j : E) := congrFun hb (e j)
      _ = v j := rfl
  have hset : b '' (↑s : Set t) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi)
      exact ⟨j, (hbe j).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e j, ?_, hbe j⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, rfl⟩)
  have hsV : b.spanIndices (↑s : Set t) = V := by
    rw [b.spanIndices_eq_span, hset, hV]
  have hproj := b.sq_sinThetaFrobenius_spanIndices_eq_sum_projection s U
  rw [hsV] at hproj
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ i ∈ s, ‖Uᗮ.starProjection (b i)‖ ^ 2 := hproj
    _ = ∑ j : κ, ‖Uᗮ.starProjection (v j)‖ ^ 2 := by
      rw [hs, Finset.sum_image (fun i _ j _ hij => e.injective hij)]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]

end Submodule

namespace TauCeti

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
  [Fintype κ]

/-! ### Contraction and Frobenius identity -/

/-- The overlap operator of two orthonormal families is a contraction. -/
theorem norm_overlapOperator_apply_le {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (a : EuclideanSpace 𝕜 κ) :
    ‖overlapOperator 𝕜 u v a‖ ≤ ‖a‖ := by
  rw [overlapOperator_def, LinearMap.comp_apply]
  refine (hu.norm_analysisMap_le _).trans_eq ?_
  rw [← hv.synthesisMapIsometry_toLinearMap, LinearIsometry.coe_toLinearMap,
    LinearIsometry.norm_map]

/-- **Frobenius identity for the overlap operator**: the squared singular values of the overlap
operator sum to the squared Frobenius norm `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` of its matrix. -/
theorem sum_sq_singularValues_overlapOperator (u : ι → E) (v : κ → E) :
    ((overlapOperator 𝕜 u v).singularValues.sum fun _ s ↦ s ^ 2) =
      ∑ j, ∑ i, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  classical
  set A := overlapOperator 𝕜 u v
  have h : ((A.singularValues.sum fun _ s ↦ s ^ 2 : ℝ) : 𝕜) =
      ((∑ j, ‖A (EuclideanSpace.basisFun κ 𝕜 j)‖ ^ 2 : ℝ) : 𝕜) :=
    A.trace_adjoint_comp_self_eq_sum_sq_singularValues.symm.trans
      (A.trace_adjoint_comp_self_eq_sum_norm_apply_sq _)
  rw [RCLike.ofReal_inj.mp h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [EuclideanSpace.basisFun_apply, overlapOperator_single, one_smul, norm_analysisMap_sq]

/-! ### Principal cosines -/

/-- The principal cosines of orthonormal finite families `u` and `v`: the singular values of their
overlap operator, in nonincreasing order and padded by zeros. These are the cosines of the
principal angles between the two spans. For arbitrary families, the singular values of the overlap
operator are `(overlapOperator 𝕜 u v).singularValues`. -/
noncomputable def cosPrincipalAngles {u : ι → E} {v : κ → E} (_hu : Orthonormal 𝕜 u)
    (_hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  (overlapOperator 𝕜 u v).singularValues

theorem cosPrincipalAngles_def {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    cosPrincipalAngles hu hv = (overlapOperator 𝕜 u v).singularValues :=
  (rfl)

/-- The principal cosines are nonnegative. -/
theorem cosPrincipalAngles_nonneg {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (k : ℕ) : 0 ≤ cosPrincipalAngles hu hv k :=
  LinearMap.singularValues_nonneg _ k

/-- The principal cosines form a nonincreasing sequence `cos θ₀ ≥ cos θ₁ ≥ ⋯`. -/
theorem cosPrincipalAngles_antitone {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : Antitone (cosPrincipalAngles hu hv) :=
  LinearMap.singularValues_antitone _

/-- Swapping the two families leaves the principal cosines unchanged. -/
theorem cosPrincipalAngles_comm {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : cosPrincipalAngles hu hv = cosPrincipalAngles hv hu := by
  rw [cosPrincipalAngles_def, cosPrincipalAngles_def, ← adjoint_overlapOperator,
    LinearMap.singularValues_adjoint]

/-- There are at most as many nonzero principal cosines as members of the second family. -/
theorem cosPrincipalAngles_of_card_le_right {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {k : ℕ} (hk : Fintype.card κ ≤ k) : cosPrincipalAngles hu hv k = 0 :=
  LinearMap.singularValues_of_finrank_le _ (by rwa [finrank_euclideanSpace])

/-- There are at most as many nonzero principal cosines as members of the first family. -/
theorem cosPrincipalAngles_of_card_le_left {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {k : ℕ} (hk : Fintype.card ι ≤ k) : cosPrincipalAngles hu hv k = 0 := by
  rw [cosPrincipalAngles_comm, cosPrincipalAngles_of_card_le_right hv hu hk]

/-- The principal cosines are at most `1`. -/
theorem cosPrincipalAngles_le_one {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (k : ℕ) : cosPrincipalAngles hu hv k ≤ 1 := by
  set A := overlapOperator 𝕜 u v
  rcases lt_or_ge k (finrank 𝕜 (EuclideanSpace 𝕜 κ)) with hk | hk
  · -- `σₖ = ‖A wₖ‖` for the `k`-th right singular vector `wₖ`, a unit vector.
    have h := A.norm_apply_rightSingularBasis ⟨k, hk⟩
    rw [Fin.val_mk] at h
    rw [cosPrincipalAngles_def, ← h]
    exact (norm_overlapOperator_apply_le hu hv _).trans_eq (A.rightSingularBasis.norm_eq_one _)
  · rw [cosPrincipalAngles_def, A.singularValues_of_finrank_le hk]
    exact zero_le_one

/-- The squared principal cosines are at most `1`, so each term `1 - cos² θₖ` of the squared
Frobenius sine is nonnegative. -/
theorem sq_cosPrincipalAngles_le_one {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (k : ℕ) : cosPrincipalAngles hu hv k ^ 2 ≤ 1 :=
  pow_le_one₀ (cosPrincipalAngles_nonneg hu hv k) (cosPrincipalAngles_le_one hu hv k)

/-- The squares of the principal cosines sum to the squared Frobenius norm `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` of
the overlap matrix. -/
theorem sum_range_sq_cosPrincipalAngles {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k ∈ Finset.range (Fintype.card κ), cosPrincipalAngles hu hv k ^ 2 =
      ∑ j, ∑ i, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [← sum_sq_singularValues_overlapOperator, ← cosPrincipalAngles_def hu hv,
    Finsupp.sum_of_support_subset _ (fun k hk ↦ Finset.mem_range.mpr ?_) _ fun _ _ ↦ by simp]
  by_contra h
  exact Finsupp.mem_support_iff.mp hk (cosPrincipalAngles_of_card_le_right hu hv (not_lt.mp h))

/-- The sum of the first `n` principal cosines is the `n`-th Ky Fan sum of the overlap operator. -/
theorem sum_range_cosPrincipalAngles_eq_kyFanSum {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (n : ℕ) :
    ∑ k ∈ Finset.range n, cosPrincipalAngles hu hv k = (overlapOperator 𝕜 u v).kyFanSum n := by
  rw [LinearMap.kyFanSum_def, cosPrincipalAngles_def]

/-! ### The squared Frobenius sine -/

/-- The squared Frobenius sine `sin²_F Θ = ∑ₖ (1 - cos² θₖ)` between the spans of two orthonormal
families of the same size `d`, summed over their first `d` principal cosines. -/
noncomputable def sinThetaSq {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card ι), (1 - cosPrincipalAngles hu hv k ^ 2)

theorem sinThetaSq_def {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv =
      ∑ k ∈ Finset.range (Fintype.card ι), (1 - cosPrincipalAngles hu hv k ^ 2) :=
  (rfl)

/-- For orthonormal families of size `d`, `sin²_F Θ = d - ∑ₖ cos² θₖ`. -/
theorem sinThetaSq_eq_card_sub_sum_sq {u v : ι → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv =
      Fintype.card ι - ∑ k ∈ Finset.range (Fintype.card ι), cosPrincipalAngles hu hv k ^ 2 := by
  simp [sinThetaSq_def, Finset.sum_sub_distrib]

/-- For orthonormal families of size `d`, `sin²_F Θ = d - ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`, the size minus the
squared Frobenius norm of the overlap matrix: the squared Frobenius sine between the spans,
computed directly from the inner products. -/
theorem sinThetaSq_eq_card_sub_sum_norm_inner_sq {u v : ι → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : sinThetaSq hu hv = Fintype.card ι - ∑ j, ∑ i, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_eq_card_sub_sum_sq, sum_range_sq_cosPrincipalAngles]

/-- Swapping the two families leaves the squared Frobenius sine unchanged. -/
theorem sinThetaSq_comm {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = sinThetaSq hv hu := by
  rw [sinThetaSq_def, sinThetaSq_def, cosPrincipalAngles_comm]

/-- The squared Frobenius sine is nonnegative. -/
theorem sinThetaSq_nonneg {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    0 ≤ sinThetaSq hu hv :=
  Finset.sum_nonneg fun k _ ↦ sub_nonneg.mpr (sq_cosPrincipalAngles_le_one hu hv k)

/-- An orthonormal family makes no angle with itself: its squared Frobenius sine vanishes. -/
@[simp]
theorem sinThetaSq_self {v : ι → E} (hv : Orthonormal 𝕜 v) : sinThetaSq hv hv = 0 := by
  classical
  rw [sinThetaSq_eq_card_sub_sum_norm_inner_sq, sub_eq_zero]
  simp [orthonormal_iff_ite.mp hv, apply_ite]

/-- All `d` principal cosines of an orthonormal family of size `d` with itself equal `1`. -/
theorem cosPrincipalAngles_self_of_lt {v : ι → E} (hv : Orthonormal 𝕜 v) {k : ℕ}
    (hk : k < Fintype.card ι) : cosPrincipalAngles hv hv k = 1 := by
  -- Every term `1 - cos² θₖ` of the vanishing sum `sin²_F Θ` is nonnegative, so each vanishes.
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
    sub_nonneg.mpr (sq_cosPrincipalAngles_le_one hv hv k)).mp
      ((sinThetaSq_def hv hv).symm.trans (sinThetaSq_self hv)) k (Finset.mem_range.mpr hk)
  rwa [sub_eq_zero, eq_comm,
    pow_eq_one_iff_of_nonneg (cosPrincipalAngles_nonneg hv hv k) two_ne_zero] at h

/-! ### The squared Frobenius sine through projections and coordinate blocks -/

/-- The squared Frobenius sine is the total squared distance of the second family from the span
`U` of the first: `sin²_F Θ = ∑ⱼ ‖P_{Uᗮ} vⱼ‖²`. -/
theorem sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq {u v : ι → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Submodule.span 𝕜 (Set.range u) = U) :
    sinThetaSq hu hv = ∑ j, ‖Uᗮ.starProjection (v j)‖ ^ 2 := by
  rw [sinThetaSq_eq_card_sub_sum_norm_inner_sq, ← Finset.card_univ, Finset.card_eq_sum_ones,
    Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- `1 = ‖vⱼ‖² = ‖P_U vⱼ‖² + ‖P_{Uᗮ} vⱼ‖²`, and `‖P_U vⱼ‖² = ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.
  rw [← hu.norm_starProjection_sq_eq_sum hU, Nat.cast_one, ← one_pow 2, ← hv.1 j,
    U.norm_sq_eq_add_norm_sq_starProjection (v j), add_sub_cancel_left]

/-- **Cross-block form of the squared Frobenius sine.** Let `u` be the members of an orthonormal
basis `b` indexed by a coordinate block `s`, and let `v` be any orthonormal family indexed by `s`.
Then `sin²_F Θ = ∑ⱼ ∑_{k ∉ s} ‖⟪bₖ, vⱼ⟫‖²`: the squared Frobenius sine is the energy of the `vⱼ` in
the complementary coordinates. -/
theorem sinThetaSq_comp_subtypeVal_eq_sum_compl_norm_inner_sq [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) {v : s → E} (hv : Orthonormal 𝕜 v) :
    sinThetaSq (b.orthonormal.comp _ Subtype.val_injective) hv =
      ∑ j, ∑ k ∈ sᶜ, ‖⟪b k, v j⟫_𝕜‖ ^ 2 := by
  have := Module.Finite.of_basis b.toBasis
  rw [sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq _ hv
    (b.span_range_comp_subtypeVal_eq_spanIndices s)]
  exact Finset.sum_congr rfl fun j _ ↦
    b.norm_starProjection_orthogonal_spanIndices_sq s (v j)

/-- **Eigenblock sine formula.** For two orthonormal bases `b` and `c` and a common coordinate block
`s`, the squared Frobenius sine between the blocks `(bᵢ)_{i ∈ s}` and `(cⱼ)_{j ∈ s}` is the
cross-block sum `∑_{j ∈ s} ∑_{k ∉ s} ‖⟪bₖ, cⱼ⟫‖²`. Applied to eigenbases of two symmetric operators,
this compares the eigenspaces selected by the same eigenvalue indices. -/
theorem sinThetaSq_comp_subtypeVal_comp_subtypeVal_eq_sum_compl_norm_inner_sq [DecidableEq ι]
    (b c : OrthonormalBasis ι 𝕜 E) (s : Finset ι) :
    sinThetaSq (b.orthonormal.comp _ Subtype.val_injective)
        (c.orthonormal.comp ((↑) : s → ι) Subtype.val_injective) =
      ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪b k, c j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_comp_subtypeVal_eq_sum_compl_norm_inner_sq]
  exact Finset.sum_coe_sort s fun j ↦ ∑ k ∈ sᶜ, ‖⟪b k, c j⟫_𝕜‖ ^ 2

end TauCeti

namespace Submodule

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι]

/-- The squared Frobenius sine of the spans of equally indexed orthonormal
families is their family-level squared Frobenius sine `TauCeti.sinThetaSq`.
The order reflects the directed projection `P_{Uᗮ} P_V`. -/
theorem sq_sinThetaFrobenius_eq_sinThetaSq_of_orthonormal
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hU : Submodule.span 𝕜 (Set.range u) = U)
    (hV : Submodule.span 𝕜 (Set.range v) = V) :
    V.sinThetaFrobenius U ^ 2 = TauCeti.sinThetaSq hu hv := by
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ j, ‖Uᗮ.starProjection (v j)‖ ^ 2 :=
      V.sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal U hv hV
    _ = TauCeti.sinThetaSq hu hv :=
      (TauCeti.sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq hu hv hU).symm

end Submodule

namespace OrthonormalBasis

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- For independently indexed coordinate blocks of two orthonormal bases, the squared
Frobenius sine is the cross-block overlap sum over the selected vectors of `b`
and the complementary vectors of `a`. The two blocks need not have equal cardinality. -/
theorem sq_sinThetaFrobenius_spanIndices (a : OrthonormalBasis ι 𝕜 E)
    (b : OrthonormalBasis κ 𝕜 E) (s : Finset ι) (t : Finset κ) :
    (b.spanIndices (↑t : Set κ)).sinThetaFrobenius
        (a.spanIndices (↑s : Set ι)) ^ 2 =
      ∑ j ∈ t, ∑ k ∈ sᶜ, ‖⟪a k, b j⟫_𝕜‖ ^ 2 := by
  classical
  calc
    (b.spanIndices (↑t : Set κ)).sinThetaFrobenius
        (a.spanIndices (↑s : Set ι)) ^ 2 =
      ∑ j ∈ t, ‖(a.spanIndices (↑s : Set ι))ᗮ.starProjection (b j)‖ ^ 2 := by
        exact b.sq_sinThetaFrobenius_spanIndices_eq_sum_projection t
          (a.spanIndices (↑s : Set ι))
    _ = ∑ j ∈ t, ∑ k ∈ sᶜ, ‖⟪a k, b j⟫_𝕜‖ ^ 2 := by
      exact Finset.sum_congr rfl fun j _ =>
        a.norm_starProjection_orthogonal_spanIndices_sq s (b j)

end OrthonormalBasis

/-! ### Principal cosines of the spans -/

namespace Orthonormal

open TauCeti

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι] [Fintype κ]

/-- **Family/subspace cosine bridge.** The principal cosines of the spans `U` and `V` of two finite
orthonormal families, the singular values of `P_V P_U`, are the principal cosines of the families,
the singular values of their overlap operator. -/
theorem principalCosines_eq_cosPrincipalAngles {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Submodule.span 𝕜 (Set.range u) = U)
    (hV : Submodule.span 𝕜 (Set.range v) = V) :
    U.principalCosines V = cosPrincipalAngles hu hv := by
  -- `P_V P_U = S_v (S_v† S_u) S_u†` for the coordinate isometries `S_u` and `S_v`, and the outer
  -- isometric factors do not change the singular values.
  have h : (U.cosThetaMap V : E →ₗ[𝕜] E) = hv.synthesisMapIsometry.toLinearMap ∘ₗ
      (overlapOperator 𝕜 v u ∘ₗ LinearMap.adjoint hu.synthesisMapIsometry.toLinearMap) := by
    rw [Submodule.cosThetaMap_def, ContinuousLinearMap.toLinearMap_comp,
      hu.toLinearMap_starProjection_eq_frameOperator hU,
      hv.toLinearMap_starProjection_eq_frameOperator hV, frameOperator_def, frameOperator_def,
      synthesisMapIsometry_toLinearMap, synthesisMapIsometry_toLinearMap, adjoint_synthesisMap,
      overlapOperator_def]
    simp only [LinearMap.comp_assoc]
  rw [Submodule.principalCosines_def, h, LinearMap.singularValues_linearIsometry_comp,
    LinearMap.singularValues_comp_adjoint_linearIsometry, cosPrincipalAngles_comm hu hv,
    cosPrincipalAngles_def]

end Orthonormal

namespace Submodule

open TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **One-dimensional cosine formula.** For unit vectors `u` and `v`, the only principal cosine of
the lines `𝕜 ∙ u` and `𝕜 ∙ v` is `‖⟪u, v⟫‖`. -/
theorem principalCosines_span_singleton {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (𝕜 ∙ u).principalCosines (𝕜 ∙ v) = Finsupp.single 0 ‖⟪u, v⟫_𝕜‖ := by
  have hu' : Orthonormal 𝕜 fun _ : Unit ↦ u := orthonormal_subsingleton_iff.mpr fun _ ↦ hu
  have hv' : Orthonormal 𝕜 fun _ : Unit ↦ v := orthonormal_subsingleton_iff.mpr fun _ ↦ hv
  rw [hu'.principalCosines_eq_cosPrincipalAngles hv' (by rw [Set.range_const])
    (by rw [Set.range_const]), cosPrincipalAngles_def,
    LinearMap.singularValues_eq_single_of_finrank_eq_one _ (by simp)
      (x := EuclideanSpace.single () 1) (by simp)]
  simp [EuclideanSpace.norm_eq]

end Submodule
