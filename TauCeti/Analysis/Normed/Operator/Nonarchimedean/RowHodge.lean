/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.RowHodge
public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row Hodge bounds for the Fredholm series of an operator

Let `u` be a continuous linear endomorphism of `C₀(I, R)` over an ultrametric norm-one Tate ring,
and fix a real additive valuation `v` and a base `b > 1` with `‖x‖ = b ^ (-v x)` for `x ≠ 0`.
Over Tate scalars the row norms `rᵢ(u)` are bounded by `‖u‖` and bound the entries of their rows,
so they are a bounded row majorant of the matrix of `u`. Hence the row Hodge heights of the row
norms lie below the Newton polygon of `det (1 - T u) = u.matrixCoeff.charPowerSeries`, and every
finite slope of that polygon is at least `-logb b ‖u‖`. For row-compact `u` this series is the
Fredholm determinant of `u`; the bounds themselves need no compactness.

## Main results

* `ContinuousLinearMap.rowHodgeHeights_rowNorm_le_newtonPolygon_charPowerSeries`: the row Hodge
  heights of the row norms lie below the Newton polygon of `det (1 - T u)`.
* `ContinuousLinearMap.neg_logb_ringOpNorm_le_unitSlope_newtonPolygon_charPowerSeries`: every
  finite slope of that Newton polygon is at least `-logb b ‖u‖`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

namespace ContinuousLinearMap

open TauCeti
open scoped ZeroAtInfty TauCeti.RingOpNorm

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R]
  {b : ℝ} {v : AddValuation R (WithTop ℝ)}

/-- If `‖x‖ = b ^ (-v x)` for `x ≠ 0` with `b > 1`, the row Hodge heights of the row norms of
`u` lie below the Newton polygon of `det (1 - T u)`. -/
theorem rowHodgeHeights_rowNorm_le_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (u : C₀(I, R) →L[R] C₀(I, R)) :
    rowHodgeHeights b u.rowNorm ≤ u.matrixCoeff.charPowerSeries.newtonPolygon v :=
  Matrix.rowHodgeHeights_le_newtonPolygon_charPowerSeries hb hv
    ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact u.rowNorm_le_ringOpNorm i⟩ u.norm_matrixCoeff_le_rowNorm

/-- If `‖x‖ = b ^ (-v x)` for `x ≠ 0` with `b > 1`, every finite slope of the Newton polygon of
`det (1 - T u)` is at least `-logb b ‖u‖`. -/
theorem neg_logb_ringOpNorm_le_unitSlope_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (u : C₀(I, R) →L[R] C₀(I, R)) {n : ℕ}
    (hn : n ∈ finiteEdges (u.matrixCoeff.charPowerSeries.newtonPolygon v)) :
    -Real.logb b ‖u‖ ≤ unitSlope (u.matrixCoeff.charPowerSeries.newtonPolygon v) n :=
  Matrix.neg_logb_le_unitSlope_newtonPolygon_charPowerSeries hb hv u.norm_matrixCoeff_le hn

end ContinuousLinearMap
