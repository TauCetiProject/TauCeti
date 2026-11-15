/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# The diagonal of an orthogonal projector

For a subspace `U` of the standard Hermitian space `EuclideanSpace 𝕜 ι`, the *projector diagonal*
`Submodule.projectorDiagonal U : ι → ℝ` is the diagonal of the matrix of the orthogonal projector
`P_U` in the standard basis `(eᵢ)`. Its entries are real, since

`(P_U eᵢ)ᵢ = ⟪eᵢ, P_U eᵢ⟫ = ‖P_U eᵢ‖²`.

They lie in `[0, 1]`, vanish exactly when `eᵢ ⊥ U` and equal `1` exactly when `eᵢ ∈ U`. They sum to
the trace of `P_U`, which is the dimension of `U`. A coordinate subspace spanned by the `eᵢ` with
`i ∈ s` has the indicator of `s` as its diagonal, and conjugating `P_U` by a diagonal unitary, that
is moving `U` by the action of the diagonal torus, does not change the diagonal.

On a Grassmannian of `r`-dimensional subspaces, identified with the coadjoint orbit of rank-`r`
projectors, the projector diagonal is the moment map of the diagonal torus action. The facts above
place its image in the hypersimplex `{x ∈ [0, 1]^ι | ∑ xᵢ = r}`, with the coordinate subspaces, the
fixed points of the torus, mapped to its vertices.

## Main definitions

* `Submodule.projectorDiagonal U`: the real diagonal of the orthogonal projector onto `U`.

## Main results

* `Submodule.projectorDiagonal_eq_norm_sq`: the entries are `‖P_U eᵢ‖²`.
* `Submodule.projectorDiagonal_nonneg`, `Submodule.projectorDiagonal_le_one`: they lie in `[0, 1]`.
* `Submodule.projectorDiagonal_eq_zero_iff`, `Submodule.projectorDiagonal_eq_one_iff`: the
  extreme values `0` and `1` are attained exactly when `eᵢ ∈ Uᗮ`, respectively `eᵢ ∈ U`.
* `Submodule.sum_projectorDiagonal`: the entries sum to the dimension of `U`.
* `Submodule.projectorDiagonal_span_single`: the diagonal of a coordinate subspace is the
  indicator of its coordinates.
* `Submodule.finrank_span_image_single`: as a consequence, a coordinate subspace has dimension
  the number of its coordinates.
* `Submodule.projectorDiagonal_map_piLpCongrRight`: the diagonal is invariant under the diagonal
  unitary group.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513 (moment maps of torus actions on coadjoint orbits).
* I. M. Gelfand, R. M. Goresky, R. D. MacPherson and V. V. Serganova, *Combinatorial geometries,
  convex polyhedra, and Schubert cells*, Adv. Math. 63 (1987), 301–316 (the diagonal of the
  projector as the moment map of a Grassmannian).
-/

public section

noncomputable section

namespace Submodule

open Module

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι))

/-- The diagonal of the orthogonal projector `P_U` onto a subspace `U` of `EuclideanSpace 𝕜 ι` in
the standard basis: its `i`-th entry is the real part of the `i`-th coordinate of `P_U eᵢ`, which
is the real number `⟪eᵢ, P_U eᵢ⟫ = ‖P_U eᵢ‖²` (`Submodule.projectorDiagonal_eq_norm_sq`). -/
def projectorDiagonal (i : ι) : ℝ :=
  RCLike.re (U.starProjection (EuclideanSpace.single i 1) i)

theorem projectorDiagonal_def (i : ι) :
    U.projectorDiagonal i = RCLike.re (U.starProjection (EuclideanSpace.single i 1) i) := (rfl)

/-- The `i`-th coordinate of `P_U eᵢ` is the squared norm of `P_U eᵢ`. -/
theorem starProjection_single_apply_self (i : ι) :
    U.starProjection (EuclideanSpace.single i 1) i =
      (‖U.starProjection (EuclideanSpace.single i (1 : 𝕜))‖ ^ 2 : ℝ) := by
  set v := EuclideanSpace.single i (1 : 𝕜)
  have h := EuclideanSpace.inner_single_left i (1 : 𝕜) (U.starProjection v)
  rw [map_one, one_mul] at h
  have h' : inner 𝕜 v (U.starProjection v) =
      inner 𝕜 (U.starProjection v) (U.starProjection v) := by
    rw [U.inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.2 (U.starProjection_apply_mem v)]
  rw [← h, h', inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

theorem projectorDiagonal_eq_norm_sq (i : ι) :
    U.projectorDiagonal i = ‖U.starProjection (EuclideanSpace.single i (1 : 𝕜))‖ ^ 2 := by
  rw [projectorDiagonal_def, starProjection_single_apply_self, RCLike.ofReal_re]

/-- The diagonal entries of `P_U` are real: as an element of `𝕜`, the `i`-th one is the `i`-th
coordinate of `P_U eᵢ`. -/
theorem ofReal_projectorDiagonal (i : ι) :
    (U.projectorDiagonal i : 𝕜) = U.starProjection (EuclideanSpace.single i 1) i := by
  rw [projectorDiagonal_eq_norm_sq, starProjection_single_apply_self]

theorem projectorDiagonal_nonneg (i : ι) : 0 ≤ U.projectorDiagonal i := by
  rw [projectorDiagonal_eq_norm_sq]
  positivity

theorem projectorDiagonal_le_one (i : ι) : U.projectorDiagonal i ≤ 1 := by
  rw [projectorDiagonal_eq_norm_sq]
  refine pow_le_one₀ (norm_nonneg _) ?_
  simpa using U.norm_starProjection_apply_le (EuclideanSpace.single i (1 : 𝕜))

/-- A diagonal entry of `P_U` vanishes exactly when the corresponding basis vector is orthogonal
to `U`. -/
@[simp]
theorem projectorDiagonal_eq_zero_iff {i : ι} :
    U.projectorDiagonal i = 0 ↔ EuclideanSpace.single i (1 : 𝕜) ∈ Uᗮ := by
  rw [projectorDiagonal_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero,
    starProjection_apply_eq_zero_iff]

/-- A diagonal entry of `P_U` equals `1` exactly when the corresponding basis vector lies
in `U`. -/
@[simp]
theorem projectorDiagonal_eq_one_iff {i : ι} :
    U.projectorDiagonal i = 1 ↔ EuclideanSpace.single i (1 : 𝕜) ∈ U := by
  rw [projectorDiagonal_eq_norm_sq, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [U.eq_starProjection_of_norm_le (w := EuclideanSpace.single i (1 : 𝕜)) (by simp [h])]
    exact U.starProjection_apply_mem _
  · simp [starProjection_eq_self_iff.2 h]

/-- The diagonal entries of the orthogonal projector onto `U` sum to the dimension of `U`, the
trace of the projector. -/
theorem sum_projectorDiagonal : ∑ i, U.projectorDiagonal i = finrank 𝕜 U := by
  have htrace : LinearMap.trace 𝕜 _ U.starProjection.toLinearMap = finrank 𝕜 U := by
    have hproj := LinearMap.isProj_range_iff_isIdempotentElem U.starProjection.toLinearMap |>.2
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap U.isIdempotentElem_starProjection)
    rw [hproj.trace, range_starProjection]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun ι 𝕜)] at htrace
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [RCLike.ofReal_sum, RCLike.ofReal_natCast, ← htrace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ofReal_projectorDiagonal, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    EuclideanSpace.inner_single_left, map_one, one_mul]

@[simp]
theorem projectorDiagonal_bot : (⊥ : Submodule 𝕜 (EuclideanSpace 𝕜 ι)).projectorDiagonal = 0 := by
  ext i
  simp [projectorDiagonal_def]

@[simp]
theorem projectorDiagonal_top : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 ι)).projectorDiagonal = 1 := by
  ext i
  exact (projectorDiagonal_eq_one_iff _).2 mem_top

/-- The diagonal of the projector onto the coordinate subspace spanned by the basis vectors `eᵢ`
with `i ∈ s` is the indicator function of `s`. -/
@[simp]
theorem projectorDiagonal_span_single (s : Set ι) :
    (span 𝕜 ((fun i ↦ EuclideanSpace.single i (1 : 𝕜)) '' s)).projectorDiagonal =
      s.indicator 1 := by
  ext i
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_mem hi, Pi.one_apply, projectorDiagonal_eq_one_iff]
    exact subset_span ⟨i, hi, rfl⟩
  · rw [Set.indicator_of_notMem hi, projectorDiagonal_eq_zero_iff]
    refine (isOrtho_iff_le.1 ((isOrtho_span).2 ?_)) (mem_span_singleton_self _)
    rintro _ hu _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff.1 hu, EuclideanSpace.inner_single_left, map_one, one_mul,
      PiLp.single_apply, ite_eq_right_iff]
    rintro rfl
    exact absurd hj hi

/-- The projector diagonal is invariant under the diagonal unitary group: moving `U` by a linear
isometry of `EuclideanSpace 𝕜 ι` acting on each coordinate separately, such as multiplication of
the coordinates by scalars of norm one, does not change the diagonal of its projector. -/
theorem projectorDiagonal_map_piLpCongrRight (e : ι → 𝕜 ≃ₗᵢ[𝕜] 𝕜) :
    (U.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
      EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι).toLinearEquiv :
        EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι)).projectorDiagonal =
      U.projectorDiagonal := by
  ext i
  set f : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι := LinearIsometryEquiv.piLpCongrRight 2 e
  rw [projectorDiagonal_eq_norm_sq, projectorDiagonal_eq_norm_sq, starProjection_map_apply,
    LinearIsometryEquiv.norm_map]
  have hsymm : f.symm (EuclideanSpace.single i 1) =
      (e i).symm 1 • EuclideanSpace.single i (1 : 𝕜) := by
    rw [LinearIsometryEquiv.piLpCongrRight_symm, LinearIsometryEquiv.piLpCongrRight_single]
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hsymm, map_smul, norm_smul, LinearIsometryEquiv.norm_map, norm_one, one_mul]

omit [Fintype ι] in
/-- The coordinate subspace spanned by the basis vectors `eᵢ` with `i ∈ s` has dimension the
cardinality of `s`. -/
@[simp]
theorem finrank_span_image_single [Finite ι] (s : Finset ι) :
    finrank 𝕜 (span 𝕜 ((fun i ↦ EuclideanSpace.single i (1 : 𝕜)) '' (s : Set ι))) = s.card := by
  have := Fintype.ofFinite ι
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_projectorDiagonal, projectorDiagonal_span_single]
  simp [Set.indicator_apply]

end Submodule
