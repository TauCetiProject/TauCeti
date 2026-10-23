/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity

/-!
# Coefficientwise base change of Fredholm series

Extending an operator on `C₀` along a bounded unital coefficient homomorphism preserves row
compactness. Each extended row norm is at most the homomorphism bound times its original row
norm. The Fredholm series of the extended operator is the coefficientwise image of the
original series, by continuity of the homomorphism on the convergent principal-minor sums.

This comparison allows coefficient rings without a common ground field and does not require
Noetherianity, flatness or a completed tensor product.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–5.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal

namespace ContinuousLinearMap

variable {I J R S : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Coefficient extension multiplies each row norm by at most the homomorphism bound. -/
theorem rowNorm_mapCoeffs_le (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) (i : I) :
    (u.mapCoeffs f C hf).rowNorm i ≤ C * u.rowNorm i := by
  apply rowNorm_le_of_forall_le (mul_nonneg C.coe_nonneg (u.rowNorm_nonneg i))
  intro j
  simp only [matrixCoeff_mapCoeffs, Matrix.map_apply]
  exact (hf _).trans (mul_le_mul_of_nonneg_left (u.norm_matrixCoeff_le_rowNorm i j) C.coe_nonneg)

/-- Row compactness is preserved by bounded coefficient extension. -/
theorem IsRowCompact.mapCoeffs {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (f : R →+* S) (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f C hf).IsRowCompact := by
  apply isRowCompact_of_norm_matrixCoeff_le
    (by simpa using hu.tendsto_rowNorm.const_mul (C : ℝ))
  intro i j
  simp only [matrixCoeff_mapCoeffs, Matrix.map_apply]
  exact (hf _).trans (mul_le_mul_of_nonneg_left (hu.norm_matrixCoeff_le_rowNorm i j) C.coe_nonneg)

/-- The Fredholm series commutes with bounded coefficient extension. This is an equality of
power series over the coefficient ring, including when that ring has nilpotents. -/
theorem IsRowCompact.charPowerSeries_map [DecidableEq I] [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (f : R →+* S) (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f C hf).matrixCoeff.charPowerSeries =
      PowerSeries.map f u.matrixCoeff.charPowerSeries := by
  rw [matrixCoeff_mapCoeffs]
  exact Matrix.charPowerSeries_map f (AddMonoidHomClass.continuous_of_bound f C hf)
    hu.summable_principalMinor

end ContinuousLinearMap
