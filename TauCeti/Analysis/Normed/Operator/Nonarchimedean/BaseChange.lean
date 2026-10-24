/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity

/-!
# Coefficientwise base change of Fredholm series

The Fredholm series of an operator on `C₀` extended along a bounded unital coefficient
homomorphism is the coefficientwise image of the original series, by continuity of the
homomorphism on the convergent principal-minor sums.

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

/-- The Fredholm series commutes with bounded coefficient extension. This is an equality of
power series over the coefficient ring, including when that ring has nilpotents. -/
theorem IsRowCompact.charPowerSeries_map [DecidableEq I] [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      PowerSeries.map f u.matrixCoeff.charPowerSeries := by
  obtain ⟨C, hC⟩ := hf
  rw [matrixCoeff_mapCoeffs]
  exact Matrix.charPowerSeries_map f (AddMonoidHomClass.continuous_of_bound f C hC)
    hu.summable_principalMinor

end ContinuousLinearMap
