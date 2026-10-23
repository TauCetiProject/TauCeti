/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact.CompletelyContinuous
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Diagonal

/-!
# Row compactness of diagonal operators

Let `R` be a seminormed ring, `I` a discrete index type and `d : I →ᵇ R` a bounded family. The
diagonal operator `ZeroAtInftyContinuousMap.diagonalCLM d` of `C₀(I, R)` has matrix
`Matrix.diagonal d`, so its `i`-th row norm is `‖d i‖`
(`ZeroAtInftyContinuousMap.rowNorm_diagonalCLM`). Hence a diagonal operator is row compact
exactly when its entries tend to zero along the cofinite filter
(`ZeroAtInftyContinuousMap.isRowCompact_diagonalCLM_iff`). Over an ultrametric ring it is then
completely continuous, and over a complete ultrametric field Serre's criterion makes complete
continuity equivalent to the decay of the entries
(`ZeroAtInftyContinuousMap.isCompletelyContinuous_diagonalCLM_iff`).

On the other hand a diagonal operator whose entries are units at infinitely many indices does not
have finite rank (`ZeroAtInftyContinuousMap.not_isFiniteRank_diagonalCLM`): its range contains
infinitely many of the linearly independent unit vectors. For a multiplicative
pseudo-uniformiser `ϖ` the diagonal operator of the family `ϖ ^ n` on `C₀(ℕ, R)` is therefore
completely continuous without having finite rank, so over an ultrametric Tate ring complete
continuity is strictly weaker than finite rank
(`ZeroAtInftyContinuousMap.exists_isCompletelyContinuous_not_isFiniteRank`).

## Main results

* `ZeroAtInftyContinuousMap.rowNorm_diagonalCLM`: the row norms are the norms of the entries.
* `ZeroAtInftyContinuousMap.isRowCompact_diagonalCLM_iff`: a diagonal operator is row compact
  exactly when its entries tend to zero.
* `ZeroAtInftyContinuousMap.isCompletelyContinuous_diagonalCLM_iff`: over a complete ultrametric
  field, the same holds for complete continuity.
* `ZeroAtInftyContinuousMap.not_isFiniteRank_diagonalCLM`: unit entries at infinitely many
  indices rule out finite rank.
* `ZeroAtInftyContinuousMap.exists_isCompletelyContinuous_not_isFiniteRank`: over an ultrametric
  Tate ring, `C₀(ℕ, R)` carries a completely continuous endomorphism of infinite rank.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §§2–3.
-/

public section

open Filter Topology ContinuousLinearMap
open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I]

section SeminormedRing

variable [SeminormedRing R]

/-- The `i`-th row norm of the diagonal operator of `d` is `‖d i‖`. -/
@[simp]
theorem rowNorm_diagonalCLM [DecidableEq I] (d : I →ᵇ R) (i : I) :
    (diagonalCLM d).rowNorm i = ‖d i‖ := by
  have h (j : I) : ‖(diagonalCLM d).matrixCoeff i j‖ ≤ ‖d i‖ := by
    by_cases hij : i = j <;> simp [hij]
  exact le_antisymm (rowNorm_le_of_forall_le (norm_nonneg _) h)
    (by simpa using norm_matrixCoeff_le_rowNorm_of_le h i)

/-- **Diagonal operators**: the diagonal operator of `d` is row compact exactly when the entries
`d i` tend to zero along the cofinite filter. -/
theorem isRowCompact_diagonalCLM_iff [DecidableEq I] {d : I →ᵇ R} :
    (diagonalCLM d).IsRowCompact ↔ Tendsto d cofinite (𝓝 0) := by
  have hrow : (diagonalCLM d).rowNorm = fun i ↦ ‖d i‖ := funext (rowNorm_diagonalCLM d)
  rw [isRowCompact_iff, hrow, ← tendsto_zero_iff_norm_tendsto_zero, and_iff_right_iff_imp]
  refine fun _ ↦ ⟨‖d‖, fun i j ↦ ?_⟩
  by_cases hij : i = j
  · simpa [hij] using d.norm_coe_le_norm j
  · simp [hij]

/-- A diagonal operator whose entries tend to zero is row compact. -/
theorem isRowCompact_diagonalCLM [DecidableEq I] {d : I →ᵇ R} (hd : Tendsto d cofinite (𝓝 0)) :
    (diagonalCLM d).IsRowCompact :=
  isRowCompact_diagonalCLM_iff.2 hd

/-- **Diagonal operators of infinite rank**: over a ring with the strong rank condition, a
diagonal operator whose entries are units at infinitely many indices does not have finite rank. -/
theorem not_isFiniteRank_diagonalCLM [StrongRankCondition R] {d : I →ᵇ R}
    (hd : {i | IsUnit (d i)}.Infinite) :
    ¬((diagonalCLM d : C₀(I, R) →L[R] C₀(I, R)) : C₀(I, R) →ₗ[R] C₀(I, R)).IsFiniteRank := by
  classical
  intro h
  obtain ⟨Q, hQ, hrange⟩ := LinearMap.isFiniteRank_iff.1 h
  refine hd ((finite_setOf_single_one_mem hQ).subset fun i hi ↦ hrange ⟨single i ↑hi.unit⁻¹, ?_⟩)
  simp

end SeminormedRing

section Ultrametric

variable [NormedRing R] [IsUltrametricDist R]

/-- Over an ultrametric ring, a diagonal operator whose entries tend to zero is completely
continuous. -/
theorem isCompletelyContinuous_diagonalCLM {d : I →ᵇ R} (hd : Tendsto d cofinite (𝓝 0)) :
    (diagonalCLM d).IsCompletelyContinuous := by
  classical
  exact (isRowCompact_diagonalCLM hd).isCompletelyContinuous

/-- **Complete continuity strictly exceeds finite rank**: over an ultrametric Tate ring with the
strong rank condition, for instance a nonzero commutative one, the diagonal operator of the
powers `ϖ ^ n` of a multiplicative pseudo-uniformiser is a completely continuous endomorphism of
`C₀(ℕ, R)` that does not have finite rank. -/
theorem exists_isCompletelyContinuous_not_isFiniteRank [TauCeti.NormedRing.IsTate R]
    [StrongRankCondition R] :
    ∃ u : C₀(ℕ, R) →L[R] C₀(ℕ, R), u.IsCompletelyContinuous ∧
      ¬(u : C₀(ℕ, R) →ₗ[R] C₀(ℕ, R)).IsFiniteRank := by
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  have hle (n : ℕ) : ‖(ϖ.unit : R) ^ n‖ ≤ 1 := by
    rw [ϖ.norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ϖ.norm_lt_one.le
  let d : ℕ →ᵇ R := .ofNormedAddCommGroupDiscrete (fun n ↦ (ϖ.unit : R) ^ n) 1 hle
  refine ⟨diagonalCLM d, isCompletelyContinuous_diagonalCLM ?_, not_isFiniteRank_diagonalCLM ?_⟩
  · rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    simpa [d, ϖ.norm_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      ϖ.norm_lt_one
  · exact Set.infinite_univ.mono fun n _ ↦ ϖ.unit.isUnit.pow n

end Ultrametric

/-- **Serre's criterion for diagonal operators**: over a complete ultrametric nontrivially normed
field, a diagonal operator is completely continuous exactly when its entries tend to zero. -/
theorem isCompletelyContinuous_diagonalCLM_iff {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {d : I →ᵇ K} :
    (diagonalCLM d).IsCompletelyContinuous ↔ Tendsto d cofinite (𝓝 0) := by
  classical
  exact isRowCompact_iff_isCompletelyContinuous.symm.trans isRowCompact_diagonalCLM_iff

end ZeroAtInftyContinuousMap
