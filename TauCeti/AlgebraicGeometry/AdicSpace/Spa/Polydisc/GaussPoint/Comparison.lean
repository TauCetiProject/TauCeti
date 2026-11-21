/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Unit

/-!
# Comparison of the one-variable and multivariate unit Gauss points

In dimension `1`, the multivariate unit Gauss point `TauCeti.ValuationSpectrum.unitGaussPoint 1 K`
of `closedPolydisc 1 K` agrees with the one-variable Gauss point `gaussPoint zero_lt_one le_rfl`
at radius `1` from `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Basic`.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: in dimension `1`,
  `unitGaussPoint 1 K` agrees with `gaussPoint zero_lt_one le_rfl`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

/-- **In dimension `1`, `unitGaussPoint 1 K` coincides with the one-variable Gauss point at radius
`1`.** -/
theorem unitGaussPoint_one_eq_gaussPoint {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  have hval : ∀ f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight,
      (closedDiscGaussValuation (R := K) zero_lt_one le_rfl f : ℝ) =
        ‖restrictedMvPowerSeriesGaussEquiv f‖ := fun f ↦ by
    refine le_antisymm ?_ ?_
    · refine closedDiscGaussValuation_le_of_forall_norm_coeff_le zero_lt_one le_rfl fun ν ↦ ?_
      rw [← coe_restrictedMvPowerSeriesGaussEquiv]
      exact MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f) ν
    · obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm
        (restrictedMvPowerSeriesGaussEquiv f)
      have hν' : ν = Finsupp.single 0 (ν 0) :=
        Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
      rw [← hν, coe_restrictedMvPowerSeriesGaussEquiv, hν']
      simpa using norm_coeff_mul_pow_le_closedDiscGaussValuation (R := K) zero_lt_one le_rfl f (ν 0)
  refine Subtype.ext (ext' fun f g ↦ ?_)
  rw [unitGaussPoint_vle_iff_norm, gaussPoint_vle_iff, ← NNReal.coe_le_coe, hval f, hval g]

end TauCeti.ValuationSpectrum
