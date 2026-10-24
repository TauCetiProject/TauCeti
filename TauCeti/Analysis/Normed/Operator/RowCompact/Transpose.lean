/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row compactness and transposed matrices

If a matrix and its transpose both represent continuous linear maps between discrete
model spaces `C₀`, one map is row compact exactly when the other is. The existence of
both maps is essential: the rows of a row-compact map need not tend to zero, whereas
the columns of every continuous linear map between model spaces do.

For a row-compact map over a complete ultrametric normed ring, a row-compact map with
transposed matrix exists exactly when each original row tends to zero. The construction
uses `Matrix.toZeroAtInftyCLM`; no alternative transpose or matrix representation is
introduced. For endomorphisms the equality of Fredholm series then follows from the
existing `Matrix.charPowerSeries_transpose`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–5.
-/

public section

namespace TauCeti

open Filter Topology ContinuousLinearMap
open scoped ZeroAtInfty

variable {I J R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

section SeminormedRing

variable [SeminormedRing R]
  {u : C₀(J, R) →L[R] C₀(I, R)} {v : C₀(I, R) →L[R] C₀(J, R)}

/-- If the transpose of the matrix of a row-compact map also represents a continuous
linear map between model spaces, that map is row compact. No Tate, completeness or
ultrametric hypothesis is needed. -/
theorem isRowCompact_of_matrixCoeff_transpose
    (htranspose : v.matrixCoeff = u.matrixCoeff.transpose) (hu : u.IsRowCompact) :
    v.IsRowCompact := by
  obtain ⟨⟨C, hC⟩, -⟩ := isRowCompact_iff.mp hu
  refine isRowCompact_iff.mpr ⟨⟨C, fun j i ↦ by simpa [htranspose] using hC i j⟩,
    tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun j ↦
      ha.trans_le (v.rowNorm_nonneg j), fun ε hε ↦ ?_⟩⟩
  -- Outside finitely many original rows, row compactness gives a uniform small bound.
  have hS : {i | ε / 2 ≤ u.rowNorm i}.Finite := by
    simpa only [not_lt] using
      eventually_cofinite.1 (hu.tendsto_rowNorm.eventually_lt_const (half_pos hε))
  -- On those finitely many rows, use the null columns of the transposed operator.
  have hv : ∀ᶠ j in cofinite, ∀ i ∈ hS.toFinset, ‖v.matrixCoeff j i‖ < ε / 2 :=
    (eventually_all_finset _).2 fun i _ ↦
      (tendsto_norm_zero.comp (v.tendsto_matrixCoeff_cofinite i)).eventually_lt_const
        (half_pos hε)
  filter_upwards [hv] with j hj
  refine lt_of_le_of_lt (rowNorm_le_of_forall_le (half_pos hε).le fun i ↦ ?_)
    (half_lt_self hε)
  by_cases hi : i ∈ hS.toFinset
  · exact (hj i hi).le
  · have hi' : u.rowNorm i < ε / 2 := not_le.1 (by simpa using hi)
    simpa [htranspose] using (hu.norm_matrixCoeff_le_rowNorm i j).trans hi'.le

/-- Row compactness is invariant under transposition whenever both matrices represent
continuous linear maps between model spaces. -/
theorem isRowCompact_iff_of_matrixCoeff_transpose
    (htranspose : v.matrixCoeff = u.matrixCoeff.transpose) :
    v.IsRowCompact ↔ u.IsRowCompact := by
  have htranspose' : u.matrixCoeff = v.matrixCoeff.transpose := by
    rw [htranspose, Matrix.transpose_transpose]
  exact ⟨isRowCompact_of_matrixCoeff_transpose htranspose',
    isRowCompact_of_matrixCoeff_transpose htranspose⟩

end SeminormedRing

section CompleteUltrametric

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  {u : C₀(J, R) →L[R] C₀(I, R)}

/-- A row-compact map has a row-compact transposed realization on `C₀` exactly when
each row of its matrix tends to zero. In particular row compactness alone does not
assert that the transposed matrix defines an operator on `C₀`. -/
theorem exists_isRowCompact_matrixCoeff_transpose_iff (hu : u.IsRowCompact) :
    (∃ v : C₀(I, R) →L[R] C₀(J, R),
      v.IsRowCompact ∧ v.matrixCoeff = u.matrixCoeff.transpose) ↔
      ∀ i, Tendsto (fun j ↦ u.matrixCoeff i j) cofinite (𝓝 0) := by
  constructor
  · rintro ⟨v, -, hv⟩ i
    simpa [hv] using v.tendsto_matrixCoeff_cofinite i
  · intro hrow
    obtain ⟨⟨C, hC⟩, -⟩ := isRowCompact_iff.mp hu
    let v := u.matrixCoeff.transpose.toZeroAtInftyCLM hrow
      ⟨C, fun j i ↦ hC i j⟩
    have hv : v.matrixCoeff = u.matrixCoeff.transpose :=
      matrixCoeff_toZeroAtInftyCLM _ _ _
    exact ⟨v, isRowCompact_of_matrixCoeff_transpose hv hu, hv⟩

end CompleteUltrametric

end TauCeti
