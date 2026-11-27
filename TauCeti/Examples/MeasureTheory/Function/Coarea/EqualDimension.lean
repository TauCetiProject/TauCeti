/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Checks for the coarea formula: equal dimensions

For a Lipschitz map `f : E → F` between finite-dimensional real inner product spaces of the same
dimension, the fibres of the coarea formula carry `H⁰`, counting measure, and the coarea Jacobian
`(Df)†.normDet` is the area Jacobian `|det Df| = (Df).normDet`. The coarea formula is then the area
formula with multiplicity: `∫_F #(s ∩ f⁻¹(y)) dy = ∫_s |det Df(x)| dx`
(`lintegral_encard_inter_preimage_eq_lintegral_normDet_fderiv`), as in
`LipschitzWith.lintegral_normDet_fderiv_eq_lintegral_encard`, which states it against `μHE[dim F]`
on `F`.
-/

public section

noncomputable section

namespace TauCeti.Examples.CoareaEqualDimension

open MeasureTheory Module Set

open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

open LipschitzWith in
/-- **The coarea formula in equal dimensions is the area formula with multiplicity**: for a
Lipschitz `f : E → F` with `dim E = dim F` and a Lebesgue-measurable `s`, the coarea formula
reads `∫_F #(s ∩ f⁻¹(y)) dy = ∫_s (Df(x)).normDet dx`, fibres counted with `H⁰ = #`. -/
theorem lintegral_encard_inter_preimage_eq_lintegral_normDet_fderiv {K : ℝ≥0} {f : E → F}
    (hf : LipschitzWith K f) (hEF : finrank ℝ E = finrank ℝ F) {s : Set E}
    (hs : NullMeasurableSet s) :
    ∫⁻ y : F, ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet := by
  have h := lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    hf hs
  rw [hEF, Nat.sub_self] at h
  simp only [euclideanHausdorffMeasure_zero_apply] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.normDet_adjoint _ hEF]

end TauCeti.Examples.CoareaEqualDimension
