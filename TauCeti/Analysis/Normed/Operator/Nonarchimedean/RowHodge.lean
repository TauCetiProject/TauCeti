/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.RowHodge
public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row Hodge lower polygons of row-compact operators

Let `K` be a normed field with an ultrametric norm, `v` a real additive valuation on `K` and
`b > 1` with `‖x‖ = b ^ (-v x)` for `x ≠ 0`. For a row-compact endomorphism `u` of `C₀(I, K)`
with row norms `rᵢ(u)`, the row Hodge polygon of the row norms, with slopes
`-logb b (r* k)` for the decreasing rearrangement `r*` of the row norms, lies below the Newton
polygon of the principal-minor series `u.matrixCoeff.charPowerSeries`
(`ContinuousLinearMap.IsRowCompact.rowHodgePolygon_rowNorm_le_newtonPolygon_charPowerSeries`).
When `K` is complete, row-compactness makes its principal-minor sums converge, and the series is
then the Fredholm series `det (1 - T u)`. The finite domain of the polygon is `[0, m]` for the
number `m` of nonzero rows, possibly infinite, so every coefficient of degree greater than `m`
vanishes.

Over a nontrivially normed field every entry of the matrix of `u` is bounded by the operator
norm. Hence, for any endomorphism `u`, the line of slope `-logb b ‖u‖` through the origin lies
below the Newton polygon of the principal-minor series `u.matrixCoeff.charPowerSeries`
(`ContinuousLinearMap.isSupportingLine_newtonPolygon_charPowerSeries`). Its coefficients are
unconditional sums of principal minors, which converge when `u` is row-compact and `K` is
complete; the series is then the Fredholm series `det (1 - T u)`. In any case every finite slope
of its Newton polygon is at least `-logb b ‖u‖`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open TauCeti
open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I] {b : ℝ}

/-- **Row Hodge lower bound for a row-compact operator.** Let `v` be a real additive valuation
on an ultrametric normed field with `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. For a
row-compact endomorphism `u` of `C₀(I, K)`, the row Hodge polygon of its row norms lies below
the Newton polygon of its principal-minor series `u.matrixCoeff.charPowerSeries`. When `K` is
complete, these principal-minor sums converge and the series is the Fredholm series
`det (1 - T u)`. -/
theorem IsRowCompact.rowHodgePolygon_rowNorm_le_newtonPolygon_charPowerSeries [NormedField K]
    [IsUltrametricDist K] {v : AddValuation K (WithTop ℝ)} {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) :
    rowHodgePolygon b u.rowNorm ≤ u.matrixCoeff.charPowerSeries.newtonPolygon v :=
  Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries hb hv
    hu.tendsto_rowNorm.bddAbove_range_of_cofinite hu.norm_matrixCoeff_le_rowNorm

/-- **Slope bound by the operator norm.** Let `v` be a real additive valuation on an ultrametric
nontrivially normed field with `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. For an
endomorphism `u` of `C₀(I, K)`, the line of slope `-logb b ‖u‖` through the origin lies below
the Newton polygon of the principal-minor series `u.matrixCoeff.charPowerSeries`, whose
coefficients are unconditional sums of principal minors of the matrix of `u`. When `u` is
row-compact and `K` is complete these sums converge and the series is the Fredholm series
`det (1 - T u)`. Since the Newton polygon starts at the origin, every finite slope is at least
`-logb b ‖u‖`. -/
theorem isSupportingLine_newtonPolygon_charPowerSeries [NontriviallyNormedField K]
    [IsUltrametricDist K] {v : AddValuation K (WithTop ℝ)} (u : C₀(I, K) →L[K] C₀(I, K))
    (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) :
    IsSupportingLine (u.matrixCoeff.charPowerSeries.newtonPolygon v) (-Real.logb b ‖u‖) 0 :=
  Matrix.isSupportingLine_newtonPolygon_charPowerSeries hb hv fun i j ↦
    (norm_matrixCoeff_le_rowNorm u i j).trans
      ((rowNorm_le_ringOpNorm u i).trans_eq (ringOpNorm_eq_opNorm u))

end ContinuousLinearMap
