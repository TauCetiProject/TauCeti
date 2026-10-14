/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BasisSpan
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
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
`cos θ₀ ≥ cos θ₁ ≥ ⋯` of the two spans (Björck–Golub). Defining them as singular values makes
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
* `TauCeti.sinThetaSq`: the squared Frobenius sine of two orthonormal families, with
  `TauCeti.sinThetaSq_eq_card_sub_sum_norm_inner_sq` and `TauCeti.sinThetaSq_self`.
* `TauCeti.sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq`: `sin²_F Θ = ∑ⱼ ‖P_{Uᗮ} vⱼ‖²`.
* `TauCeti.sinThetaSq_comp_subtypeVal_eq_sum_compl_norm_inner_sq` and
  `TauCeti.sinThetaSq_comp_subtypeVal_comp_subtypeVal_eq_sum_compl_norm_inner_sq`: the cross-block
  form of the squared Frobenius sine for coordinate blocks of orthonormal bases.

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
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- The orthogonal complement of the block span is the span of the complementary block.
  have hc : Submodule.span 𝕜 (Set.range (b ∘ ((↑) : (sᶜ : Finset ι) → ι))) =
      (b.spanIndices s)ᗮ := by
    rw [b.orthogonal_spanIndices, ← Finset.coe_compl, b.span_range_comp_subtypeVal_eq_spanIndices]
  rw [(b.orthonormal.comp _ Subtype.val_injective).norm_starProjection_sq_eq_sum hc]
  exact Finset.sum_coe_sort sᶜ fun k ↦ ‖⟪b k, v j⟫_𝕜‖ ^ 2

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
