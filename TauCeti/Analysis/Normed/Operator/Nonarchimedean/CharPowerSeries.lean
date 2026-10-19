/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.GaussContinuity
public import TauCeti.Analysis.Normed.Operator.RowCompact.Sequence

/-!
# Continuity of Fredholm series in operator norm

A norm-convergent sequence of row-compact operators on `C₀(I, R)` has determinants converging
in every positive-radius Gauss norm. This continuity permits finite determinant identities to
pass to limits of row-compact operators.

The determinant is `u.matrixCoeff.charPowerSeries`.
Scalars may be complete ultrametric norm-one Tate rings, not just fields.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

namespace TauCeti

open Filter Finset Topology ContinuousLinearMap
open scoped ZeroAtInfty RingOpNorm

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [NormedRing.IsTate R]
  {u : C₀(I, R) →L[R] C₀(I, R)} {v : ℕ → C₀(I, R) →L[R] C₀(I, R)}

/-- The Fredholm series of a norm-convergent sequence of row-compact operators converge in
Gauss norm at every positive radius. Unlike coefficientwise convergence of arbitrary entire
series, operator-norm convergence supplies uniform control of the determinant tails. -/
theorem tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendsto_ringOpNorm
    [CompleteSpace R] [NormOneClass R] (h : Tendsto (fun n ↦ ‖u - v n‖) atTop (𝓝 0))
    (hv : ∀ n, (v n).IsRowCompact) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n ↦ ((v n).matrixCoeff.charPowerSeries -
      u.matrixCoeff.charPowerSeries).gaussNorm norm ρ) atTop (𝓝 0) := by
  obtain ⟨r, _, hr, hu, hv⟩ := exists_common_row_majorant_of_tendsto_ringOpNorm h hv
  refine tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendstoUniformly hv hu hr ?_ hρ
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [h.eventually_lt_const hε] with n hn
  intro p
  simpa only [dist_eq_norm, matrixCoeff_sub, Matrix.sub_apply] using
    ((u - v n).norm_matrixCoeff_le p.1 p.2).trans_lt hn

end TauCeti
