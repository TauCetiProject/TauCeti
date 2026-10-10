/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic

/-!
# Finite Gromov–Wasserstein objectives

The distortion of a finite transport matrix is exactly the weighted four-index sum of kernel
discrepancies. At exponent two this is the usual quadratic objective in the coupling entries.
The infimum over these matrices is the generic measured-kernel Gromov–Wasserstein distance;
there is no extra factor of `1 / 2`.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Definition 11 and §5.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace TauCeti

variable {ι κ Z : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSpace κ]
  [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
  {μ : PMF ι} {ν : PMF κ}

section EDist

variable [EDist Z]

/-- For a finite nonzero exponent, the powered distortion is the four-index matrix objective.
The target and its distances may be extended-valued. -/
theorem TransportMatrix.gromovWassersteinDistortion_rpow (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ^ p.toReal =
      ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ p.toReal * A i j * A i' j' := by
  rw [gromovWassersteinDistortion_def,
    eLpNorm_rpow_eq_lintegral hp0 hp (measurable_of_countable _).aemeasurable,
    lintegral_countable', tsum_fintype]
  simp only [Fintype.sum_prod_type, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    TransportMatrix.toPMF_apply, mul_assoc]

/-- The square of the two-distortion is the standard nonconvex quadratic GW objective. -/
theorem TransportMatrix.gromovWassersteinDistortion_sq (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) :
    gromovWassersteinDistortion 2 ωX ωY A.toPMF.toMeasure ^ 2 =
      ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' := by
  simpa using A.gromovWassersteinDistortion_rpow ωX ωY (p := 2) (by norm_num) (by norm_num)

/-- Infimizing the finite matrix distortions gives exactly the generic GW distance. -/
theorem gromovWassersteinEDist_eq_iInf_transportMatrix (p : ℝ≥0∞)
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist p μ.toMeasure ωX ν.toMeasure ωY =
      ⨅ A : TransportMatrix μ ν, gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure := by
  refine le_antisymm (le_iInf fun A ↦ gromovWassersteinEDist_le
    A.isCoupling_toPMF_toMeasure p ωX ωY) (le_gromovWassersteinEDist fun π hπ ↦ ?_)
  obtain ⟨A, rfl⟩ := hπ.exists_transportMatrix
  exact iInf_le _ A

/-- The finite GW problem is the infimum of the weighted four-index objectives. -/
theorem gromovWassersteinEDist_rpow_eq_iInf_transportMatrix {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist p μ.toMeasure ωX ν.toMeasure ωY ^ p.toReal =
      ⨅ A : TransportMatrix μ ν, ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ p.toReal * A i j * A i' j' := by
  rw [gromovWassersteinEDist_eq_iInf_transportMatrix,
    ← ENNReal.orderIsoRpow_apply p.toReal (ENNReal.toReal_pos hp0 hp), OrderIso.map_iInf]
  exact iInf_congr fun A ↦ A.gromovWassersteinDistortion_rpow ωX ωY hp0 hp

/-- Squared GW distance is the infimum of the quadratic matrix objective. -/
theorem gromovWassersteinEDist_sq_eq_iInf_transportMatrix
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist 2 μ.toMeasure ωX ν.toMeasure ωY ^ 2 =
      ⨅ A : TransportMatrix μ ν, ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' := by
  simpa using gromovWassersteinEDist_rpow_eq_iInf_transportMatrix (p := 2)
    (by norm_num) (by norm_num) μ ωX ν ωY

end EDist

/-- For metric-valued matrices, the finite quadratic objective can be read entirely in `ℝ`. -/
theorem TransportMatrix.toReal_gromovWassersteinDistortion_sq [PseudoMetricSpace Z]
    (A : TransportMatrix μ ν) (ωX : ι × ι → Z) (ωY : κ × κ → Z) :
    (gromovWassersteinDistortion 2 ωX ωY A.toPMF.toMeasure).toReal ^ 2 =
      ∑ i, ∑ j, ∑ i', ∑ j',
        dist (ωX (i, i')) (ωY (j, j')) ^ 2 * (A i j).toReal * (A i' j').toReal := by
  have hfin : ∀ i j i' j',
      edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' ≠ ∞ := by
    intros
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (edist_ne_top _ _))
      (A.apply_ne_top _ _)) (A.apply_ne_top _ _)
  have h := congrArg ENNReal.toReal (A.gromovWassersteinDistortion_sq ωX ωY)
  simpa (disch := simp [ENNReal.sum_ne_top, hfin]) only [ENNReal.toReal_sum,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ← dist_edist] using h

end TauCeti
