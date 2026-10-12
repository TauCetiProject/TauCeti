/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The overlap operator of two finite families and their principal cosines

For finite families `u : ι → E` and `v : κ → E` in an inner product space, the *overlap operator*
is analysis by `u` after synthesis by `v`,

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
`d - ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.

The definitions make sense for arbitrary finite families; the statements that need orthonormality
assume it.

## Main declarations

* `TauCeti.overlapOperator`: the overlap operator of two finite families.
* `TauCeti.overlapOperator_eq_toEuclideanLin`: its matrix is `(⟪uᵢ, vⱼ⟫)ᵢⱼ`.
* `TauCeti.adjoint_synthesisMap_comp_synthesisMap`: it is `S_u† S_v`.
* `TauCeti.adjoint_overlapOperator`: swapping the families gives the adjoint.
* `TauCeti.norm_overlapOperator_apply_le`: for orthonormal families it is a contraction.
* `TauCeti.sum_sq_singularValues_overlapOperator`: `∑ₖ σₖ² = ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.
* `TauCeti.cosPrincipalAngles`: the principal cosines, as singular values of the overlap operator,
  with `cosPrincipalAngles_nonneg`, `cosPrincipalAngles_le_one`, `cosPrincipalAngles_antitone`
  and `cosPrincipalAngles_comm`.
* `TauCeti.sinThetaSq`: the squared Frobenius sine, with
  `TauCeti.sinThetaSq_eq_card_sub_sum_norm_inner_sq` and `TauCeti.sinThetaSq_self`.

## References

* Å. Björck and G. H. Golub, *Numerical methods for computing angles between linear subspaces*,
  Math. Comp. 27 (1973), 579–594.
* G. H. Golub and C. F. Van Loan, *Matrix Computations*, fourth edition, Johns Hopkins University
  Press, 2013, Section 6.4.3.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype κ]

/-! ### The overlap operator -/

variable (𝕜) in
/-- The overlap operator of finite families `u : ι → E` and `v : κ → E`: analysis by `u` after
synthesis by `v`, with matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` (`TauCeti.overlapOperator_eq_toEuclideanLin`). -/
noncomputable def overlapOperator (u : ι → E) (v : κ → E) :
    EuclideanSpace 𝕜 κ →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  analysisMap 𝕜 u ∘ₗ synthesisMap 𝕜 v

theorem overlapOperator_def (u : ι → E) (v : κ → E) :
    overlapOperator 𝕜 u v = analysisMap 𝕜 u ∘ₗ synthesisMap 𝕜 v :=
  (rfl)

@[simp]
theorem overlapOperator_apply (u : ι → E) (v : κ → E) (a : EuclideanSpace 𝕜 κ) (i : ι) :
    overlapOperator 𝕜 u v a i = ∑ j, ⟪u i, v j⟫_𝕜 * a j := by
  simp [overlapOperator_def, mul_comm]

/-- The overlap operator sends the `j`-th coordinate vector, scaled by `c`, to `c` times the
coefficients `(⟪uᵢ, vⱼ⟫)ᵢ` of `vⱼ`. -/
@[simp]
theorem overlapOperator_single [DecidableEq κ] (u : ι → E) (v : κ → E) (j : κ) (c : 𝕜) :
    overlapOperator 𝕜 u v (EuclideanSpace.single j c) = c • analysisMap 𝕜 u (v j) := by
  rw [overlapOperator_def, LinearMap.comp_apply, synthesisMap_single, map_smul]

/-- The overlap operator is the matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` acting on coefficient space. -/
theorem overlapOperator_eq_toEuclideanLin [DecidableEq κ] (u : ι → E) (v : κ → E) :
    overlapOperator 𝕜 u v = Matrix.toEuclideanLin (Matrix.of fun i j ↦ ⟪u i, v j⟫_𝕜) := by
  ext a i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

variable [Fintype ι]

/-- The overlap operator of a family with itself is its Gram operator. -/
@[simp]
theorem overlapOperator_self (v : ι → E) : overlapOperator 𝕜 v v = gramOperator 𝕜 v := by
  rw [overlapOperator_def, gramOperator_def]

/-- The overlap operators in the two orders are adjoint to each other:
`⟪O_{v,u} b, a⟫ = ⟪b, O_{u,v} a⟫`. -/
theorem inner_overlapOperator_left (u : ι → E) (v : κ → E) (b : EuclideanSpace 𝕜 ι)
    (a : EuclideanSpace 𝕜 κ) :
    ⟪overlapOperator 𝕜 v u b, a⟫_𝕜 = ⟪b, overlapOperator 𝕜 u v a⟫_𝕜 := by
  rw [overlapOperator_def, overlapOperator_def, LinearMap.comp_apply, LinearMap.comp_apply,
    ← inner_synthesisMap_left u b, ← inner_conj_symm (synthesisMap 𝕜 u b),
    inner_synthesisMap_left v a, inner_conj_symm]

/-- Swapping the two families gives the adjoint overlap operator. -/
@[simp]
theorem adjoint_overlapOperator (u : ι → E) (v : κ → E) :
    LinearMap.adjoint (overlapOperator 𝕜 u v) = overlapOperator 𝕜 v u :=
  ((LinearMap.eq_adjoint_iff _ _).mpr (inner_overlapOperator_left u v)).symm

/-- In a finite-dimensional space the overlap operator is `S_u† S_v` for the synthesis maps `S_u`
and `S_v`; for orthonormal families these are the coordinate isometries
`Orthonormal.synthesisMapIsometry`. -/
theorem adjoint_synthesisMap_comp_synthesisMap [FiniteDimensional 𝕜 E] (u : ι → E) (v : κ → E) :
    LinearMap.adjoint (synthesisMap 𝕜 u) ∘ₗ synthesisMap 𝕜 v = overlapOperator 𝕜 u v := by
  rw [adjoint_synthesisMap, overlapOperator_def]

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

variable (𝕜) in
/-- The principal cosines of finite families `u` and `v`: the singular values of their overlap
operator, in nonincreasing order and padded by zeros. For orthonormal families these are the
cosines of the principal angles between the two spans; the results below that need it assume
orthonormality. -/
noncomputable def cosPrincipalAngles (u : ι → E) (v : κ → E) : ℕ →₀ ℝ :=
  (overlapOperator 𝕜 u v).singularValues

theorem cosPrincipalAngles_def (u : ι → E) (v : κ → E) :
    cosPrincipalAngles 𝕜 u v = (overlapOperator 𝕜 u v).singularValues :=
  (rfl)

theorem cosPrincipalAngles_nonneg (u : ι → E) (v : κ → E) (k : ℕ) :
    0 ≤ cosPrincipalAngles 𝕜 u v k :=
  LinearMap.singularValues_nonneg _ k

theorem cosPrincipalAngles_antitone (u : ι → E) (v : κ → E) :
    Antitone (cosPrincipalAngles 𝕜 u v) :=
  LinearMap.singularValues_antitone _

/-- Swapping the two families leaves the principal cosines unchanged. -/
theorem cosPrincipalAngles_comm (u : ι → E) (v : κ → E) :
    cosPrincipalAngles 𝕜 u v = cosPrincipalAngles 𝕜 v u := by
  rw [cosPrincipalAngles_def, cosPrincipalAngles_def, ← adjoint_overlapOperator,
    LinearMap.singularValues_adjoint]

/-- There are at most as many nonzero principal cosines as members of the second family. -/
theorem cosPrincipalAngles_of_card_le_right (u : ι → E) (v : κ → E) {k : ℕ}
    (hk : Fintype.card κ ≤ k) : cosPrincipalAngles 𝕜 u v k = 0 :=
  LinearMap.singularValues_of_finrank_le _ (by rwa [finrank_euclideanSpace])

/-- There are at most as many nonzero principal cosines as members of the first family. -/
theorem cosPrincipalAngles_of_card_le_left (u : ι → E) (v : κ → E) {k : ℕ}
    (hk : Fintype.card ι ≤ k) : cosPrincipalAngles 𝕜 u v k = 0 := by
  rw [cosPrincipalAngles_comm, cosPrincipalAngles_of_card_le_right v u hk]

/-- The principal cosines of two orthonormal families are at most `1`. -/
theorem cosPrincipalAngles_le_one {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (k : ℕ) : cosPrincipalAngles 𝕜 u v k ≤ 1 := by
  set A := overlapOperator 𝕜 u v
  rcases lt_or_ge k (finrank 𝕜 (EuclideanSpace 𝕜 κ)) with hk | hk
  · -- `σₖ = ‖A wₖ‖` for the `k`-th right singular vector `wₖ`, a unit vector.
    have h := A.norm_apply_rightSingularBasis ⟨k, hk⟩
    rw [Fin.val_mk] at h
    rw [cosPrincipalAngles_def, ← h]
    exact (norm_overlapOperator_apply_le hu hv _).trans_eq (A.rightSingularBasis.norm_eq_one _)
  · rw [cosPrincipalAngles_def, A.singularValues_of_finrank_le hk]
    exact zero_le_one

/-- The squared principal cosines of two orthonormal families are at most `1`, so each term
`1 - cos² θₖ` of the squared Frobenius sine is nonnegative. -/
theorem sq_cosPrincipalAngles_le_one {u : ι → E} {v : κ → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (k : ℕ) : cosPrincipalAngles 𝕜 u v k ^ 2 ≤ 1 :=
  pow_le_one₀ (cosPrincipalAngles_nonneg u v k) (cosPrincipalAngles_le_one hu hv k)

/-- The squares of the principal cosines sum to the squared Frobenius norm `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` of
the overlap matrix. -/
theorem sum_range_sq_cosPrincipalAngles (u : ι → E) (v : κ → E) :
    ∑ k ∈ Finset.range (Fintype.card κ), cosPrincipalAngles 𝕜 u v k ^ 2 =
      ∑ j, ∑ i, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [← sum_sq_singularValues_overlapOperator, ← cosPrincipalAngles_def,
    Finsupp.sum_of_support_subset _ (fun k hk ↦ Finset.mem_range.mpr ?_) _ fun _ _ ↦ by simp]
  by_contra h
  exact Finsupp.mem_support_iff.mp hk (cosPrincipalAngles_of_card_le_right u v (not_lt.mp h))

/-! ### The squared Frobenius sine -/

variable (𝕜) in
/-- The squared Frobenius sine `sin²_F Θ = ∑ₖ (1 - cos² θₖ)` of two finite families of the same
size `d`, the sum running over the first `d` principal cosines. -/
noncomputable def sinThetaSq (u v : ι → E) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card ι), (1 - cosPrincipalAngles 𝕜 u v k ^ 2)

theorem sinThetaSq_def (u v : ι → E) :
    sinThetaSq 𝕜 u v =
      ∑ k ∈ Finset.range (Fintype.card ι), (1 - cosPrincipalAngles 𝕜 u v k ^ 2) :=
  (rfl)

/-- For families of size `d`, `sin²_F Θ = d - ∑ₖ cos² θₖ`. -/
theorem sinThetaSq_eq_card_sub_sum_sq (u v : ι → E) :
    sinThetaSq 𝕜 u v =
      Fintype.card ι - ∑ k ∈ Finset.range (Fintype.card ι), cosPrincipalAngles 𝕜 u v k ^ 2 := by
  simp [sinThetaSq_def, Finset.sum_sub_distrib]

/-- For families of size `d`, `sin²_F Θ = d - ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`: the squared Frobenius sine is
the size minus the squared Frobenius norm of the overlap matrix. -/
theorem sinThetaSq_eq_card_sub_sum_norm_inner_sq (u v : ι → E) :
    sinThetaSq 𝕜 u v = Fintype.card ι - ∑ j, ∑ i, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_eq_card_sub_sum_sq, sum_range_sq_cosPrincipalAngles]

/-- Swapping the two families leaves the squared Frobenius sine unchanged. -/
theorem sinThetaSq_comm (u v : ι → E) : sinThetaSq 𝕜 u v = sinThetaSq 𝕜 v u := by
  rw [sinThetaSq_def, sinThetaSq_def, cosPrincipalAngles_comm]

/-- The squared Frobenius sine of two orthonormal families is nonnegative. -/
theorem sinThetaSq_nonneg {u v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    0 ≤ sinThetaSq 𝕜 u v :=
  Finset.sum_nonneg fun k _ ↦ sub_nonneg.mpr (sq_cosPrincipalAngles_le_one hu hv k)

/-- An orthonormal family makes no angle with itself: its squared Frobenius sine vanishes. -/
@[simp]
theorem sinThetaSq_self {v : ι → E} (hv : Orthonormal 𝕜 v) : sinThetaSq 𝕜 v v = 0 := by
  classical
  rw [sinThetaSq_eq_card_sub_sum_norm_inner_sq, sub_eq_zero]
  simp [orthonormal_iff_ite.mp hv, apply_ite]

/-- All `d` principal cosines of an orthonormal family of size `d` with itself equal `1`. -/
theorem cosPrincipalAngles_self_of_lt {v : ι → E} (hv : Orthonormal 𝕜 v) {k : ℕ}
    (hk : k < Fintype.card ι) : cosPrincipalAngles 𝕜 v v k = 1 := by
  -- Every term `1 - cos² θₖ` of the vanishing sum `sin²_F Θ` is nonnegative, so each vanishes.
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
    sub_nonneg.mpr (sq_cosPrincipalAngles_le_one hv hv k)).mp
      ((sinThetaSq_def v v).symm.trans (sinThetaSq_self hv)) k (Finset.mem_range.mpr hk)
  rwa [sub_eq_zero, eq_comm,
    pow_eq_one_iff_of_nonneg (cosPrincipalAngles_nonneg v v k) two_ne_zero] at h

end TauCeti
