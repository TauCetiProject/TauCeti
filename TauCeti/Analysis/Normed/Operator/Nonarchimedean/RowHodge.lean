/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.RowHodge
public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row Hodge lower polygons of operators on model spaces

For a continuous linear endomorphism `u` of a model space `C₀(I, R)` over Tate scalars, the row
norms `rᵢ(u)` of its matrix form a row majorant bounded by the operator norm. Given a real
additive valuation `v` and a base `b > 1` with `b ^ (-v x) ≤ ‖x‖` for nonzero `x`, the row
Hodge polygon of the row norms, with weights `-logb b` of their decreasing rearrangement, lies
below the Newton polygon of the Fredholm series `det (1 - X u)`. For a row-compact `u` the row
norms tend to zero, so the weights tend to infinity whenever infinitely many row norms are
positive. Consequently every finite slope of that Newton polygon is at least `-logb b ‖u‖`.

## Main results

* `ContinuousLinearMap.rowHodgePolygon_rowNorm_le_newtonPolygon`: the row Hodge polygon of the
  row norms lies below the Newton polygon of the Fredholm series.
* `ContinuousLinearMap.neg_logb_ringOpNorm_le_unitSlope_newtonPolygon`: every finite slope of
  the Newton polygon of the Fredholm series is at least `-logb b ‖u‖`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open TauCeti
open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R]
  {v : AddValuation R (WithTop ℝ)} {b : ℝ}

/-- **Row Hodge lower bound for an operator.** If `‖x‖ ≥ b ^ (-v x)` for nonzero `x`, the row
Hodge polygon of the row norms of `u` lies below the Newton polygon of `det (1 - X u)`. -/
theorem rowHodgePolygon_rowNorm_le_newtonPolygon (hb : 1 < b)
    (hv : ∀ x ≠ 0, b ^ (-(v x).untop₀) ≤ ‖x‖) (u : C₀(I, R) →L[R] C₀(I, R)) :
    rowHodgePolygon b u.rowNorm ≤ u.matrixCoeff.charPowerSeries.newtonPolygon v :=
  Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries hb hv
    ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact u.rowNorm_le_ringOpNorm i⟩ u.norm_matrixCoeff_le_rowNorm

/-- **Lower bound for Fredholm slopes of an operator.** If `‖x‖ ≥ b ^ (-v x)` for nonzero `x`,
every finite slope of the Newton polygon of `det (1 - X u)` is at least `-logb b ‖u‖`. -/
theorem neg_logb_ringOpNorm_le_unitSlope_newtonPolygon (hb : 1 < b)
    (hv : ∀ x ≠ 0, b ^ (-(v x).untop₀) ≤ ‖x‖) (u : C₀(I, R) →L[R] C₀(I, R)) {n : ℕ}
    (hn : n ∈ finiteEdges (u.matrixCoeff.charPowerSeries.newtonPolygon v)) :
    -Real.logb b ‖u‖ ≤ unitSlope (u.matrixCoeff.charPowerSeries.newtonPolygon v) n :=
  Matrix.neg_logb_le_unitSlope_newtonPolygon_charPowerSeries hb hv
    (fun i j ↦ (u.norm_matrixCoeff_le_rowNorm i j).trans (u.rowNorm_le_ringOpNorm i)) hn

end ContinuousLinearMap
