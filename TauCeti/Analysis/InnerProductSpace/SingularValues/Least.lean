/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The least singular value: the minimal stretch of a linear map

For a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
**minimal stretch** `ℓ(A) = A.minimalStretch` is the last of the `n = dim E` singular values of
`A`, `σₙ(A)` in one-based numbering, which is `A.singularValues (n - 1)` in Mathlib's zero-based
numbering. It is the least factor by which `A` stretches a unit vector:

  `ℓ(A) = min {‖A v‖ : ‖v‖ = 1}`,

the quantity `ℓ(T)` of Martio, Rickman and Väisälä. Together with the operator norm
`‖A‖ = σ₁(A)`, the largest singular value, it measures how far `A` is from a multiple of an
isometry: `ℓ(A) ≤ ‖A‖`, with equality exactly for `A = 0` and the conformal maps. The quotients
`‖A‖ / ℓ(A)` and the products of the intermediate singular values are the linear distortions in
the theory of quasiregular maps.

When `E = 0` the index `n - 1` is `0` and `ℓ(A) = 0`; the characterisations as a minimum over
unit vectors therefore assume `Nontrivial E`.

## Main declarations

* `LinearMap.minimalStretch`: the minimal stretch `ℓ(A) = σₙ(A)`.
* `LinearMap.minimalStretch_mul_norm_le_norm_apply`: `ℓ(A) ‖v‖ ≤ ‖A v‖` for every `v`.
* `LinearMap.le_minimalStretch_iff`: `c ≤ ℓ(A)` if and only if `c ‖v‖ ≤ ‖A v‖` for every `v`.
* `LinearMap.exists_mem_sphere_norm_apply_eq_minimalStretch`: on a nonzero space, `ℓ(A)` is
  attained at a unit vector, the last right singular vector
  (`LinearMap.norm_apply_rightSingularBasis_eq_minimalStretch`).
* `LinearMap.isLeast_minimalStretch`: `ℓ(A)` is the least value of `‖A v‖` on the unit sphere.
* `LinearMap.minimalStretch_le_norm`, `LinearMap.minimalStretch_eq_norm_iff`: `ℓ(A) ≤ ‖A‖`, with
  equality if and only if `A = 0` or `A` is conformal.
* `LinearMap.minimalStretch_pos_iff`: `0 < ℓ(A)` if and only if `A` is injective;
  `LinearMap.minimalStretch_eq_zero_of_not_injective`: `ℓ(A) = 0` when `A` is not injective.
* `LinearMap.minimalStretch_mul_norm_symm`: `ℓ(A) ‖A⁻¹‖ = 1` for a linear equivalence `A`.
* `LinearMap.minimalStretch_mul_le_minimalStretch_comp`: `ℓ(B) ℓ(A) ≤ ℓ(B ∘ A)`.
* `LinearMap.minimalStretch_pow_le_normDet`: `ℓ(A)ⁿ ≤ normDet(A)`; the upper bound
  `normDet(A) ≤ ‖A‖ⁿ` is `ContinuousLinearMap.normDet_le_norm_pow`.
* `LinearMap.norm_mul_minimalStretch_pow_le_normDet`,
  `LinearMap.normDet_le_norm_pow_mul_minimalStretch`: the sharper sandwich
  `‖A‖ ℓ(A)ⁿ⁻¹ ≤ normDet(A) ≤ ‖A‖ⁿ⁻¹ ℓ(A)`, the latter for `n > 0`;
  `LinearMap.minimalStretch_pos_of_normDet_ne_zero`: hence `normDet(A) ≠ 0` gives `ℓ(A) > 0`.
* `LinearMap.minimalStretch_smul`, `LinearMap.minimalStretch_linearIsometry_comp`,
  `LinearMap.minimalStretch_comp_linearIsometryEquiv`: `ℓ(c A) = ‖c‖ ℓ(A)`, and `ℓ` is unchanged
  by linear isometries on the left and isometric isomorphisms on the right.
* `LinearMap.lipschitzWith_minimalStretch`: `ℓ` is `1`-Lipschitz for the operator norm, by
  Weyl's perturbation bound `LinearMap.abs_singularValues_sub_singularValues_le`; hence it is
  continuous and Borel measurable.
* `Submodule.minimalStretch_starProjection_eq_zero`: the orthogonal projection onto a proper
  subspace has minimal stretch `0`.

## References

* O. Martio, S. Rickman and J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), Section 2 (the quantity `ℓ(T)`).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.3 (the smallest singular value).
-/

public section

open Module

namespace LinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- The **minimal stretch** `ℓ(A)` of a linear map `A : E →ₗ[𝕜] F` between finite-dimensional
inner product spaces: the smallest of the `n = dim E` singular values of `A`, the singular value
at the zero-based index `n - 1`. For `E ≠ 0` it is the minimum of `‖A v‖` over unit vectors `v`
(`LinearMap.isLeast_minimalStretch`); for `E = 0` it is `0`. -/
noncomputable def minimalStretch (A : E →ₗ[𝕜] F) : ℝ :=
  A.singularValues (finrank 𝕜 E - 1)

/-- The minimal stretch is the singular value at the zero-based index `dim E - 1`. -/
theorem minimalStretch_def (A : E →ₗ[𝕜] F) :
    A.minimalStretch = A.singularValues (finrank 𝕜 E - 1) :=
  (rfl)

/-- The minimal stretch is nonnegative. -/
theorem minimalStretch_nonneg (A : E →ₗ[𝕜] F) : 0 ≤ A.minimalStretch :=
  A.singularValues_nonneg _

/-- On the zero space the minimal stretch is `0`. -/
@[simp]
theorem minimalStretch_of_subsingleton [Subsingleton E] (A : E →ₗ[𝕜] F) :
    A.minimalStretch = 0 :=
  A.singularValues_of_finrank_le (by simp [finrank_zero_of_subsingleton])

/-- The minimal stretch is at most each of the `dim E` singular values. -/
theorem minimalStretch_le_singularValues (A : E →ₗ[𝕜] F) {i : ℕ} (hi : i < finrank 𝕜 E) :
    A.minimalStretch ≤ A.singularValues i :=
  A.singularValues_antitone (by omega)

/-- `A` stretches its last right singular vector by exactly the minimal stretch. -/
theorem norm_apply_rightSingularBasis_eq_minimalStretch (A : E →ₗ[𝕜] F)
    {i : Fin (finrank 𝕜 E)} (hi : (i : ℕ) = finrank 𝕜 E - 1) :
    ‖A (A.rightSingularBasis i)‖ = A.minimalStretch := by
  rw [norm_apply_rightSingularBasis, minimalStretch_def, hi]

/-- `A` stretches every vector by at least the minimal stretch: `ℓ(A) ‖v‖ ≤ ‖A v‖`. -/
theorem minimalStretch_mul_norm_le_norm_apply (A : E →ₗ[𝕜] F) (v : E) :
    A.minimalStretch * ‖v‖ ≤ ‖A v‖ :=
  A.singularValues_mul_norm_le_norm_apply <|
    A.rightSingularBasis.mem_spanIndices_iff.mpr fun i hi ↦
      absurd (Nat.le_sub_one_of_lt i.isLt) hi

/-- On a nonzero space, the minimal stretch is attained at a unit vector, namely the last right
singular vector. -/
theorem exists_mem_sphere_norm_apply_eq_minimalStretch [Nontrivial E] (A : E →ₗ[𝕜] F) :
    ∃ v ∈ Metric.sphere (0 : E) 1, ‖A v‖ = A.minimalStretch :=
  ⟨A.rightSingularBasis ⟨_, Nat.sub_one_lt finrank_pos.ne'⟩, by simp,
    A.norm_apply_rightSingularBasis_eq_minimalStretch rfl⟩

/-- On a nonzero space, `c ≤ ℓ(A)` exactly when `A` stretches every vector by at least `c`. -/
theorem le_minimalStretch_iff [Nontrivial E] (A : E →ₗ[𝕜] F) {c : ℝ} :
    c ≤ A.minimalStretch ↔ ∀ v, c * ‖v‖ ≤ ‖A v‖ := by
  refine ⟨fun h v ↦ (mul_le_mul_of_nonneg_right h (norm_nonneg v)).trans
    (A.minimalStretch_mul_norm_le_norm_apply v), fun h ↦ ?_⟩
  obtain ⟨v, hv, hAv⟩ := A.exists_mem_sphere_norm_apply_eq_minimalStretch
  simpa [mem_sphere_zero_iff_norm.mp hv, hAv] using h v

/-- On a nonzero space, the minimal stretch is the least value of `‖A v‖` over unit vectors `v`;
it is attained at the last right singular vector. -/
theorem isLeast_minimalStretch [Nontrivial E] (A : E →ₗ[𝕜] F) :
    IsLeast ((fun v ↦ ‖A v‖) '' Metric.sphere 0 1) A.minimalStretch := by
  refine ⟨A.exists_mem_sphere_norm_apply_eq_minimalStretch, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  simpa [mem_sphere_zero_iff_norm.mp hv] using A.minimalStretch_mul_norm_le_norm_apply v

/-- The minimal stretch is at most the operator norm. -/
theorem minimalStretch_le_norm (A : E →ₗ[𝕜] F) :
    A.minimalStretch ≤ ‖toContinuousLinearMap A‖ := by
  rw [norm_toContinuousLinearMap_eq_singularValues_zero]
  exact A.singularValues_antitone (Nat.zero_le _)

/-- The minimal stretch equals the operator norm exactly when `A = 0` or `A` is conformal, that
is, a nonzero multiple of a linear isometry. -/
theorem minimalStretch_eq_norm_iff (A : E →ₗ[𝕜] F) :
    A.minimalStretch = ‖toContinuousLinearMap A‖ ↔
      A = 0 ∨ IsConformalMap (toContinuousLinearMap A) := by
  nontriviality E
  rw [← map_eq_zero_iff toContinuousLinearMap toContinuousLinearMap.injective,
    ← (toContinuousLinearMap A).normDet_eq_norm_pow_iff, coe_toContinuousLinearMap]
  refine ⟨fun h ↦ A.normDet_eq_pow_finrank_of_norm_eq fun v ↦ le_antisymm ?_ ?_, fun h ↦ ?_⟩
  · exact (toContinuousLinearMap A).le_opNorm v
  · exact h ▸ A.minimalStretch_mul_norm_le_norm_apply v
  · refine le_antisymm A.minimalStretch_le_norm <| (A.le_minimalStretch_iff).mpr fun v ↦ ?_
    exact ((toContinuousLinearMap A).norm_apply_eq_of_normDet_eq_norm_pow h v).ge

/-- On a nonzero space, the minimal stretch is positive exactly when `A` is injective. -/
theorem minimalStretch_pos_iff [Nontrivial E] (A : E →ₗ[𝕜] F) :
    0 < A.minimalStretch ↔ Function.Injective A := by
  refine ⟨fun h ↦ A.injective_iff_forall_lt_finrank_singularValues_pos.mpr fun i hi ↦
    h.trans_le (A.minimalStretch_le_singularValues hi), fun h ↦ ?_⟩
  obtain ⟨v, hv, hAv⟩ := A.exists_mem_sphere_norm_apply_eq_minimalStretch
  exact hAv ▸ norm_pos_iff.mpr
    ((map_ne_zero_iff A h).mpr (ne_zero_of_mem_sphere one_ne_zero ⟨v, hv⟩))

/-- A linear map that is not injective has minimal stretch `0`. -/
theorem minimalStretch_eq_zero_of_not_injective (A : E →ₗ[𝕜] F)
    (h : ¬ Function.Injective A) : A.minimalStretch = 0 := by
  nontriviality E
  exact le_antisymm (not_lt.1 (mt A.minimalStretch_pos_iff.1 h)) A.minimalStretch_nonneg

/-- On a nonzero space, the minimal stretch of a linear equivalence is the reciprocal of the
operator norm of its inverse: `ℓ(A) ‖A⁻¹‖ = 1`. -/
theorem minimalStretch_mul_norm_symm [Nontrivial E] (A : E ≃ₗ[𝕜] F) :
    (A : E →ₗ[𝕜] F).minimalStretch * ‖toContinuousLinearMap (A.symm : F →ₗ[𝕜] E)‖ = 1 := by
  set ℓ := (A : E →ₗ[𝕜] F).minimalStretch
  have hℓ : 0 < ℓ := ((A : E →ₗ[𝕜] F).minimalStretch_pos_iff).mpr A.injective
  refine le_antisymm ?_ ?_
  · -- `‖A⁻¹ y‖ ≤ ℓ⁻¹ ‖y‖`, since `ℓ ‖A⁻¹ y‖ ≤ ‖A (A⁻¹ y)‖ = ‖y‖`.
    rw [← le_inv_mul_iff₀ hℓ, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hℓ.le) fun y ↦ ?_
    rw [inv_mul_eq_div, le_div_iff₀' hℓ]
    simpa using (A : E →ₗ[𝕜] F).minimalStretch_mul_norm_le_norm_apply (A.symm y)
  · -- A unit vector `v` with `‖A v‖ = ℓ` gives `1 = ‖A⁻¹ (A v)‖ ≤ ‖A⁻¹‖ ℓ`.
    obtain ⟨v, hv, hAv⟩ := (A : E →ₗ[𝕜] F).exists_mem_sphere_norm_apply_eq_minimalStretch
    have h := (toContinuousLinearMap (A.symm : F →ₗ[𝕜] E)).le_opNorm (A v)
    simp only [coe_toContinuousLinearMap', LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      mem_sphere_zero_iff_norm.mp hv] at h hAv
    rwa [hAv, mul_comm] at h

/-- The minimal stretch is supermultiplicative: `ℓ(B) ℓ(A) ≤ ℓ(B ∘ A)`. -/
theorem minimalStretch_mul_le_minimalStretch_comp (B : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) :
    B.minimalStretch * A.minimalStretch ≤ (B ∘ₗ A).minimalStretch := by
  nontriviality E
  refine ((B ∘ₗ A).le_minimalStretch_iff).mpr fun v ↦ ?_
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (A.minimalStretch_mul_norm_le_norm_apply v)
    B.minimalStretch_nonneg).trans (B.minimalStretch_mul_norm_le_norm_apply (A v))

/-- The `n`-th power of the minimal stretch is at most the Jacobian `normDet`, `n = dim E`. -/
theorem minimalStretch_pow_le_normDet (A : E →ₗ[𝕜] F) :
    A.minimalStretch ^ finrank 𝕜 E ≤ A.normDet :=
  A.pow_finrank_le_normDet_of_mul_norm_le A.minimalStretch_nonneg
    A.minimalStretch_mul_norm_le_norm_apply

/-- On a nonzero space of dimension `n`, the Jacobian `normDet` is at most `‖A‖ⁿ⁻¹ ℓ(A)`: in
terms of the singular values, `σ₁ ⋯ σₙ ≤ σ₁ⁿ⁻¹ σₙ`. In dimension `0` the right side is `0`
while `normDet(A) = 1`. -/
theorem normDet_le_norm_pow_mul_minimalStretch (hE : 0 < finrank 𝕜 E) (A : E →ₗ[𝕜] F) :
    A.normDet ≤ ‖toContinuousLinearMap A‖ ^ (finrank 𝕜 E - 1) * A.minimalStretch := by
  rw [normDet_eq_prod_singularValues, norm_toContinuousLinearMap_eq_singularValues_zero,
    minimalStretch_def]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hE.ne'
  rw [hm, Nat.add_sub_cancel, Finset.prod_range_succ]
  refine mul_le_mul_of_nonneg_right ?_ (A.singularValues_nonneg m)
  exact (Finset.prod_le_prod₀ (fun i _ ↦ A.singularValues_nonneg i)
    fun i _ ↦ A.singularValues_antitone (Nat.zero_le i)).trans_eq (by simp)

/-- The Jacobian `normDet` is at least `‖A‖ ℓ(A)ⁿ⁻¹`, `n = dim E`: in terms of the singular
values, `σ₁ σₙⁿ⁻¹ ≤ σ₁ ⋯ σₙ`. -/
theorem norm_mul_minimalStretch_pow_le_normDet (A : E →ₗ[𝕜] F) :
    ‖toContinuousLinearMap A‖ * A.minimalStretch ^ (finrank 𝕜 E - 1) ≤ A.normDet := by
  rw [normDet_eq_prod_singularValues, norm_toContinuousLinearMap_eq_singularValues_zero,
    minimalStretch_def]
  rcases h : finrank 𝕜 E with - | m
  · simp [A.singularValues_of_finrank_le h.le]
  rw [Nat.add_sub_cancel, Finset.prod_range_succ', mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (A.singularValues_nonneg 0)
  refine (Finset.prod_le_prod₀ (fun _ _ ↦ A.singularValues_nonneg m)
    fun i hi ↦ A.singularValues_antitone ?_).trans_eq' (by simp)
  simp only [Finset.mem_range] at hi
  omega

/-- On a nonzero space, a map with nonzero Jacobian `normDet` has positive minimal stretch. -/
theorem minimalStretch_pos_of_normDet_ne_zero (hE : 0 < finrank 𝕜 E) {A : E →ₗ[𝕜] F}
    (h : A.normDet ≠ 0) : 0 < A.minimalStretch := by
  refine A.minimalStretch_nonneg.lt_of_ne fun h0 ↦ h (le_antisymm ?_ A.normDet_nonneg)
  simpa [← h0] using A.normDet_le_norm_pow_mul_minimalStretch hE

/-- The zero map has minimal stretch `0`. -/
@[simp]
theorem minimalStretch_zero : (0 : E →ₗ[𝕜] F).minimalStretch = 0 := by
  simp [minimalStretch_def]

/-- On a nonzero space, the identity has minimal stretch `1`. -/
@[simp]
theorem minimalStretch_id [Nontrivial E] : (id : E →ₗ[𝕜] E).minimalStretch = 1 :=
  le_antisymm ((minimalStretch_le_norm _).trans
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by simp))
    ((le_minimalStretch_iff _).mpr fun v ↦ by simp)

/-- Scaling a map by `c` scales its minimal stretch by `‖c‖`. -/
@[simp]
theorem minimalStretch_smul (c : 𝕜) (A : E →ₗ[𝕜] F) :
    (c • A).minimalStretch = ‖c‖ * A.minimalStretch := by
  simp [minimalStretch_def]

/-- Negating a map leaves its minimal stretch unchanged. -/
@[simp]
theorem minimalStretch_neg (A : E →ₗ[𝕜] F) : (-A).minimalStretch = A.minimalStretch := by
  rw [← neg_one_smul 𝕜 A, minimalStretch_smul, norm_neg, norm_one, one_mul]

/-- Composing on the left with a linear isometry leaves the minimal stretch unchanged. -/
@[simp]
theorem minimalStretch_linearIsometry_comp (W : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    (W.toLinearMap ∘ₗ A).minimalStretch = A.minimalStretch := by
  simp [minimalStretch_def]

/-- Composing on the left with an isometric isomorphism leaves the minimal stretch unchanged. -/
@[simp]
theorem minimalStretch_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    ((U : F →ₗ[𝕜] G) ∘ₗ A).minimalStretch = A.minimalStretch :=
  minimalStretch_linearIsometry_comp U.toLinearIsometry A

/-- Composing on the right with an isometric isomorphism leaves the minimal stretch unchanged. -/
@[simp]
theorem minimalStretch_comp_linearIsometryEquiv (A : E →ₗ[𝕜] F) (U : G ≃ₗᵢ[𝕜] E) :
    (A ∘ₗ (U : G →ₗ[𝕜] E)).minimalStretch = A.minimalStretch := by
  simp [minimalStretch_def, U.toLinearEquiv.finrank_eq]

/-- **Perturbation bound.** The minimal stretch is a `1`-Lipschitz function of a continuous
linear map: `|ℓ(A) - ℓ(B)| ≤ ‖A - B‖`. -/
theorem lipschitzWith_minimalStretch :
    LipschitzWith 1 fun A : E →L[𝕜] F ↦ (A : E →ₗ[𝕜] F).minimalStretch :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa [minimalStretch_def, Real.dist_eq, dist_eq_norm, toContinuousLinearMap_coe] using
      abs_singularValues_sub_singularValues_le (A : E →ₗ[𝕜] F) B (finrank 𝕜 E - 1)

/-- The minimal stretch is a continuous function of a continuous linear map. -/
theorem continuous_minimalStretch :
    Continuous fun A : E →L[𝕜] F ↦ (A : E →ₗ[𝕜] F).minimalStretch :=
  lipschitzWith_minimalStretch.continuous

/-- The minimal stretch is a Borel measurable function of a continuous linear map. -/
theorem measurable_minimalStretch [MeasurableSpace (E →L[𝕜] F)]
    [OpensMeasurableSpace (E →L[𝕜] F)] :
    Measurable fun A : E →L[𝕜] F ↦ (A : E →ₗ[𝕜] F).minimalStretch :=
  continuous_minimalStretch.measurable

end LinearMap

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {V : Submodule 𝕜 E}

/-- The orthogonal projection onto a proper subspace `V` has minimal stretch zero: it is not
injective. -/
theorem minimalStretch_starProjection_eq_zero (hV : V ≠ ⊤) :
    ((V.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E).minimalStretch = 0 :=
  LinearMap.minimalStretch_eq_zero_of_not_injective _ <| by
    rw [← LinearMap.ker_eq_bot]
    exact V.ker_starProjection.trans_ne (orthogonal_eq_bot_iff.not.2 hV)

end Submodule
