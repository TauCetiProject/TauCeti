/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Diagonal
public import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Coordinate projections in a Hilbert basis

For a Hilbert basis `b : HilbertBasis ι 𝕜 E` and a set `s` of indices, `b.projection s` is the
orthogonal projection onto the closed span of the basis vectors `b i` with `i ∈ s`: it keeps the
coordinates `⟪b i, x⟫` with `i ∈ s` and replaces the others by zero. It is the diagonal operator
`b.diagonal` whose entries are the indicator function of `s`, so it is defined for every set `s`,
and it has finite rank when `s` is finite. The complementary projection is
`b.projection sᶜ = 1 - b.projection s`.

When `b` is an eigenbasis of a nonnegative self-adjoint operator `A` with eigenvalues `w i`, the
projection onto the indices with `w i ≤ R` is the spectral cutoff of `A` at `R`, and the
complementary projection is controlled by the quadratic form of `A`: if `R ≤ w i` for every
`i ∈ s` and `0 ≤ w i` for the other indices, then

`R ‖b.projection s x‖² ≤ ∑ i, w i ‖⟪b i, x⟫‖²`

(`HilbertBasis.mul_norm_projection_sq_le`). For a bounded operator `T` this bounds
`T - T ∘ b.projection sᶜ` from the form domain of `A` to the target by `‖T‖ / √R`
(`HilbertBasis.mul_norm_apply_projection_sq_le`). This is how a bounded operator is approximated,
in the operator norm from the form domain, by the finite-rank operators `T ∘ b.projection sᶜ`
built from finitely many eigenvectors.

## Main declarations

* `HilbertBasis.projection`: the coordinate projection onto the closed span of `b i`, `i ∈ s`,
  with `HilbertBasis.projection_eq_diagonal` relating it to `HilbertBasis.diagonal`.
* `HilbertBasis.repr_projection`, `HilbertBasis.projection_apply_self`,
  `HilbertBasis.hasSum_projection`, `HilbertBasis.projection_eq_sum`: its coordinates, its values
  on the basis and its expansion in the basis.
* `HilbertBasis.projection_mul_projection`, `HilbertBasis.commute_projection`,
  `HilbertBasis.isIdempotentElem_projection`, `HilbertBasis.isSymmetric_projection`,
  `HilbertBasis.projection_compl`: it is an orthogonal projection, and these projections form a
  Boolean algebra of commuting projections.
* `HilbertBasis.isStarProjection_projection`, `HilbertBasis.adjoint_projection`,
  `HilbertBasis.projection_eq_starProjection`: in a complete space it is the star projection
  onto the closure of the span of `b '' s`.
* `HilbertBasis.hasSum_norm_projection_sq`, `HilbertBasis.norm_projection_le`: the norm of the
  projection of a vector, and the bound `‖b.projection s‖ ≤ 1`.
* `HilbertBasis.hasFiniteRange_projection`: the projection has finite rank for finite `s`.
* `HilbertBasis.mul_norm_projection_sq_le`, `HilbertBasis.mul_norm_apply_projection_sq_le`: the
  weighted bounds above.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  §II.3 (orthonormal bases) and §VI.5 (compact operators as norm limits of finite-rank operators).
-/

public section

noncomputable section

open RCLike
open scoped InnerProductSpace lp ENNReal

namespace HilbertBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (b : HilbertBasis ι 𝕜 E) (s t : Set ι)

/-- The **coordinate projection** of the Hilbert basis `b` onto the indices in `s`: the orthogonal
projection onto the closed span of the basis vectors `b i` with `i ∈ s`, which keeps the
coordinates `⟪b i, x⟫` with `i ∈ s` and replaces the others by zero. It is the diagonal operator
whose entries are the indicator function of `s`. -/
def projection : E →L[𝕜] E :=
  b.diagonal ⟨s.indicator 1, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s <;> simp [hi]⟩⟩

/-- The coordinate projection is the diagonal operator whose entries are the indicator function
of `s`. -/
theorem projection_eq_diagonal (hs : Memℓp (s.indicator (1 : ι → 𝕜)) ∞) :
    b.projection s = b.diagonal ⟨s.indicator 1, hs⟩ := by
  rw [projection]

/-- The coordinates of `b.projection s x` are those of `x` on `s` and zero off `s`. -/
@[simp]
theorem repr_projection (x : E) (i : ι) :
    b.repr (b.projection s x) i = s.indicator (b.repr x) i := by
  by_cases hi : i ∈ s <;> simp [projection, hi]

/-- The coordinates of `b.projection s x`, in the form `⟪b i, b.projection s x⟫`. -/
@[simp]
theorem inner_projection_right (x : E) (i : ι) :
    ⟪b i, b.projection s x⟫_𝕜 = s.indicator (fun i ↦ ⟪b i, x⟫_𝕜) i := by
  by_cases hi : i ∈ s <;> simp [← b.repr_apply_apply, hi]

/-- The coordinate projection keeps the basis vectors indexed by `s` and kills the others. -/
@[simp]
theorem projection_apply_self (i : ι) : b.projection s (b i) = s.indicator b i := by
  by_cases hi : i ∈ s <;> simp [projection, hi]

/-- The expansion of `b.projection s x` in the basis: the terms `⟪b i, x⟫ • b i` with `i ∈ s`. -/
theorem hasSum_projection (x : E) :
    HasSum (fun i ↦ s.indicator (fun i ↦ ⟪b i, x⟫_𝕜 • b i) i) (b.projection s x) := by
  convert b.hasSum_repr (b.projection s x) using 1
  ext i
  by_cases hi : i ∈ s <;> simp [hi, ← b.repr_apply_apply]

/-- For a finite set of indices the coordinate projection is the finite sum
`∑ i ∈ s, ⟪b i, x⟫ • b i`. -/
theorem projection_eq_sum (s : Finset ι) (x : E) :
    b.projection s x = ∑ i ∈ s, ⟪b i, x⟫_𝕜 • b i := by
  rw [← Finset.sum_congr rfl fun i hi ↦
    Set.indicator_of_mem (Finset.mem_coe.2 hi) (fun i ↦ ⟪b i, x⟫_𝕜 • b i)]
  exact (b.hasSum_projection s x).unique
    (hasSum_sum_of_ne_finset_zero fun i hi ↦ Set.indicator_of_notMem (by simpa using hi) _)

/-- Two coordinate projections in the same basis multiply to the projection onto the
intersection. -/
@[simp]
theorem projection_mul_projection : b.projection s * b.projection t = b.projection (s ∩ t) := by
  ext1 x
  apply b.repr.injective
  ext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht]

/-- Two coordinate projections in the same basis compose to the projection onto the
intersection. -/
@[simp]
theorem projection_comp_projection :
    b.projection s ∘L b.projection t = b.projection (s ∩ t) :=
  b.projection_mul_projection s t

/-- Coordinate projections in the same basis commute. -/
theorem commute_projection : Commute (b.projection s) (b.projection t) := by
  rw [Commute, SemiconjBy, projection_mul_projection, projection_mul_projection, Set.inter_comm]

/-- The coordinate projection is idempotent. -/
theorem isIdempotentElem_projection : IsIdempotentElem (b.projection s) := by
  rw [IsIdempotentElem, projection_mul_projection, Set.inter_self]

/-- The coordinate projection onto all indices is the identity. -/
@[simp]
theorem projection_univ : b.projection Set.univ = 1 := by
  ext1 x
  apply b.repr.injective
  ext i
  simp

/-- The coordinate projection onto no index is zero. -/
@[simp]
theorem projection_empty : b.projection ∅ = 0 := by
  ext1 x
  apply b.repr.injective
  ext i
  simp

/-- The coordinate projections onto complementary sets of indices add up to the identity. -/
theorem projection_compl : b.projection sᶜ = 1 - b.projection s := by
  ext1 x
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- The coordinate projection is symmetric: `⟪b.projection s x, y⟫ = ⟪x, b.projection s y⟫`. -/
theorem isSymmetric_projection : (b.projection s : E →ₗ[𝕜] E).IsSymmetric := by
  intro x y
  -- Both sides are the Parseval sum `∑_{i ∈ s} conj ⟪b i, x⟫ ⟪b i, y⟫`.
  have key (x y : E) : HasSum (fun i ↦ s.indicator (fun i ↦ ⟪x, b i⟫_𝕜 * ⟪b i, y⟫_𝕜) i)
      ⟪x, b.projection s y⟫_𝕜 := by
    convert b.hasSum_inner_mul_inner x (b.projection s y) using 1
    ext i
    by_cases hi : i ∈ s <;> simp [inner_projection_right, hi]
  have hstar : HasSum (fun i ↦ s.indicator (fun i ↦ ⟪x, b i⟫_𝕜 * ⟪b i, y⟫_𝕜) i)
      (star ⟪y, b.projection s x⟫_𝕜) := by
    convert (key y x).star using 1
    ext i
    by_cases hi : i ∈ s <;> simp [hi, mul_comm]
  simpa only [ContinuousLinearMap.coe_coe, ← starRingEnd_apply, inner_conj_symm] using
    hstar.unique (key x y)

/-- The squared norm of `b.projection s x` is the sum of the squared coordinates of `x` on `s`. -/
theorem hasSum_norm_projection_sq (x : E) :
    HasSum (fun i ↦ s.indicator (fun i ↦ ‖⟪b i, x⟫_𝕜‖ ^ 2) i) (‖b.projection s x‖ ^ 2) := by
  convert b.hasSum_norm_sq_inner (b.projection s x) using 1
  ext i
  by_cases hi : i ∈ s <;> simp [inner_projection_right, hi]

/-- The coordinate projection is a contraction. -/
theorem norm_projection_le : ‖b.projection s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    refine hasSum_le (fun i ↦ ?_) (b.hasSum_norm_projection_sq s x) (b.hasSum_norm_sq_inner x)
    by_cases hi : i ∈ s <;> simp [hi]

/-- The coordinate projection onto a finite set of indices has finite rank. -/
theorem hasFiniteRange_projection (hs : s.Finite) :
    (b.projection s : E →ₗ[𝕜] E).HasFiniteRange :=
  b.hasFiniteRange_of_apply_eq_zero _ hs.toFinset fun i hi ↦ by
    simp [Set.indicator_of_notMem (by simpa using hi : i ∉ s)]

section CompleteSpace

variable [CompleteSpace E]

/-- In a complete space the coordinate projection is a star projection. -/
theorem isStarProjection_projection : IsStarProjection (b.projection s) :=
  ⟨b.isIdempotentElem_projection s,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (b.isSymmetric_projection s)⟩

/-- The coordinate projection is self-adjoint. -/
@[simp]
theorem adjoint_projection : (b.projection s).adjoint = b.projection s :=
  (b.isStarProjection_projection s).isSelfAdjoint.adjoint_eq

/-- The coordinate projection is the orthogonal projection onto the closure of the span of the
basis vectors `b i` with `i ∈ s`. -/
theorem projection_eq_starProjection :
    b.projection s = (Submodule.span 𝕜 (b '' s)).topologicalClosure.starProjection := by
  set S := Submodule.span 𝕜 (b '' s)
  have hbS {i : ι} (hi : i ∈ s) : b i ∈ S.topologicalClosure :=
    S.le_topologicalClosure (Submodule.subset_span ⟨i, hi, rfl⟩)
  ext1 x
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_).symm
  · refine S.isClosed_topologicalClosure.mem_of_tendsto (b.hasSum_projection s x)
      (Filter.Eventually.of_forall fun F ↦ Submodule.sum_mem _ fun i _ ↦ ?_)
    by_cases hi : i ∈ s
    · simpa [hi] using Submodule.smul_mem _ ⟪b i, x⟫_𝕜 (hbS hi)
    · simp [hi]
  · have hx : x - b.projection s x = b.projection sᶜ x := by simp [projection_compl]
    rw [hx, ← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      (Submodule.isClosed_orthogonal _) hw
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      ← ContinuousLinearMap.coe_coe, b.isSymmetric_projection]
    simp [hi]

end CompleteSpace

/-- **Weighted bound for a coordinate projection.** Let `w` be a family of weights with
`c ≤ w i` for `i ∈ s` and `0 ≤ w i` for `i ∉ s`. If the weighted sum of the squared coordinates
of `x` is `q`, then `c ‖b.projection s x‖² ≤ q`. For `w` the eigenvalues of a nonnegative operator
in the eigenbasis `b`, `q` is its quadratic form at `x`. -/
theorem mul_norm_projection_sq_le {w : ι → ℝ} {c q : ℝ} (hc : ∀ i ∈ s, c ≤ w i)
    (hw : ∀ i ∉ s, 0 ≤ w i) {x : E} (hq : HasSum (fun i ↦ w i * ‖⟪b i, x⟫_𝕜‖ ^ 2) q) :
    c * ‖b.projection s x‖ ^ 2 ≤ q := by
  refine hasSum_le (fun i ↦ ?_) ((b.hasSum_norm_projection_sq s x).mul_left c) hq
  by_cases hi : i ∈ s
  · simpa [hi] using mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg ‖⟪b i, x⟫_𝕜‖)
  · simpa [hi] using mul_nonneg (hw i hi) (sq_nonneg ‖⟪b i, x⟫_𝕜‖)

/-- **Truncation estimate.** Under the hypotheses of `HilbertBasis.mul_norm_projection_sq_le`
with `0 ≤ c`, a bounded operator `T` satisfies `c ‖T (b.projection s x)‖² ≤ ‖T‖² q`. Applied to
`s = {i | R < w i}`, this bounds the difference `T x - T (b.projection {i | w i ≤ R} x)` between `T`
and its finite-rank truncation by `‖T‖ / √R` times the form norm `√q` of `x`. -/
theorem mul_norm_apply_projection_sq_le {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] (T : E →L[𝕜] F) {w : ι → ℝ} {c q : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ i ∈ s, c ≤ w i) (hw : ∀ i ∉ s, 0 ≤ w i) {x : E}
    (hq : HasSum (fun i ↦ w i * ‖⟪b i, x⟫_𝕜‖ ^ 2) q) :
    c * ‖T (b.projection s x)‖ ^ 2 ≤ ‖T‖ ^ 2 * q := by
  calc c * ‖T (b.projection s x)‖ ^ 2 ≤ c * (‖T‖ ^ 2 * ‖b.projection s x‖ ^ 2) := by
        gcongr
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
    _ = ‖T‖ ^ 2 * (c * ‖b.projection s x‖ ^ 2) := by ring
    _ ≤ ‖T‖ ^ 2 * q := by gcongr; exact b.mul_norm_projection_sq_le s hc hw hq

end HilbertBasis
