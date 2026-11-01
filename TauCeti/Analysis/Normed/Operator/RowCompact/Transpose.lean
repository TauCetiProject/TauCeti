/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row compactness and bounded transposition

If two continuous linear maps between discrete `C₀` model spaces have transposed matrices,
then one is row compact exactly when the other is. The existence of both maps matters:
row compactness alone does not make the transposed matrix act on `C₀`, since a row of the
original matrix need not tend to zero.

For a row-compact map over a complete ultrametric normed ring, null rows are precisely the
condition for a row-compact transposed realization to exist. The realization is supplied by
`Matrix.toZeroAtInftyCLM`; no new transpose construction is needed. For endomorphisms,
`Matrix.charPowerSeries_transpose` already gives equality of their principal-minor series.

## Main results

* `ContinuousLinearMap.IsRowCompact.of_matrixCoeff_transpose`: transfer row compactness to
  an existing transposed realization.
* `ContinuousLinearMap.isRowCompact_iff_of_matrixCoeff_transpose`: the symmetric comparison.
* `ContinuousLinearMap.IsRowCompact.exists_matrixCoeff_transpose_iff`: a row-compact transpose
  exists exactly when every row tends to zero.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–5.
-/

public section

open Filter Topology
open scoped ZeroAtInfty Matrix

namespace ContinuousLinearMap

variable {I J R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

section SeminormedRing

variable [SeminormedRing R]

/-- A bounded transposed realization of a row-compact map is row compact. Both maps must act
on `C₀`: the transpose of a general row-compact matrix need not have null columns. -/
theorem IsRowCompact.of_matrixCoeff_transpose {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {v : C₀(I, R) →L[R] C₀(J, R)}
    (hv : v.matrixCoeff = u.matrixCoeffᵀ) : v.IsRowCompact := by
  obtain ⟨C, hC⟩ := (isRowCompact_iff.mp hu).1
  refine isRowCompact_iff.mpr ⟨⟨C, fun j i ↦ by simpa [hv] using hC i j⟩,
    tendsto_order.mpr ⟨fun a ha ↦ Eventually.of_forall fun j ↦
      ha.trans_le (v.rowNorm_nonneg j), fun ε hε ↦ ?_⟩⟩
  -- Outside finitely many original rows, row decay controls every entry at once.
  let S := {i | ¬u.rowNorm i < ε / 2}
  have hS : S.Finite := eventually_cofinite.mp
    (hu.tendsto_rowNorm.eventually_lt_const (half_pos hε))
  -- On the remaining rows, the null columns of the transposed realization suffice.
  have hsmall : ∀ᶠ j in cofinite, ∀ i ∈ S, ‖v.matrixCoeff j i‖ < ε / 2 :=
    hS.eventually_all.mpr fun i _ ↦
      (v.tendsto_matrixCoeff_cofinite i).norm.eventually_lt_const (by
        simpa using half_pos hε)
  filter_upwards [hsmall] with j hj
  refine lt_of_le_of_lt (v.rowNorm_le_of_forall_le (half_pos hε).le fun i ↦ ?_)
    (half_lt_self hε)
  by_cases hi : i ∈ S
  · exact (hj i hi).le
  · have hi' : u.rowNorm i < ε / 2 := by simpa [S] using hi
    simpa [hv] using (hu.norm_matrixCoeff_le_rowNorm i j).trans hi'.le

/-- Two maps with transposed matrices are row compact simultaneously. This does not assert
that an arbitrary row-compact map admits a transpose acting on `C₀`. -/
theorem isRowCompact_iff_of_matrixCoeff_transpose {u : C₀(J, R) →L[R] C₀(I, R)}
    {v : C₀(I, R) →L[R] C₀(J, R)} (hv : v.matrixCoeff = u.matrixCoeffᵀ) :
    u.IsRowCompact ↔ v.IsRowCompact := by
  refine ⟨fun hu ↦ hu.of_matrixCoeff_transpose hv, fun hv' ↦
    hv'.of_matrixCoeff_transpose ?_⟩
  simp [hv]

end SeminormedRing

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- A row-compact map admits a row-compact transposed realization exactly when each of its
rows tends to zero. Neither Tate scalars nor a Noetherian hypothesis is required. -/
theorem IsRowCompact.exists_matrixCoeff_transpose_iff {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) :
    (∃ v : C₀(I, R) →L[R] C₀(J, R), v.matrixCoeff = u.matrixCoeffᵀ ∧ v.IsRowCompact) ↔
      ∀ i, Tendsto (fun j ↦ u.matrixCoeff i j) cofinite (𝓝 0) := by
  constructor
  · rintro ⟨v, hv, _⟩ i
    simpa [hv] using v.tendsto_matrixCoeff_cofinite i
  · intro hrow
    have hbdd : ∃ C, ∀ j i, ‖u.matrixCoeffᵀ j i‖ ≤ C := by
      obtain ⟨C, hC⟩ := (isRowCompact_iff.mp hu).1
      exact ⟨C, fun j i ↦ hC i j⟩
    let v := u.matrixCoeffᵀ.toZeroAtInftyCLM hrow hbdd
    have hv : v.matrixCoeff = u.matrixCoeffᵀ := matrixCoeff_toZeroAtInftyCLM _ _ _
    exact ⟨v, hv, hu.of_matrixCoeff_transpose hv⟩

end ContinuousLinearMap
