/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

import TauCeti.Analysis.InnerProductSpace.Positive.Basic

/-!
# Defect-operator completion of a Gaussian contraction

For a contraction `D : F →L[ℝ] E` between finite-dimensional real inner product spaces,
adding an independent standard Gaussian transformed by the defect operator
`CFC.sqrt (1 - D ∘L D.adjoint)` to the image under `D` gives a standard Gaussian on `E`.
The identity `ContinuousLinearMap.map_add_defect_stdGaussian` includes singular contractions
and zero-dimensional spaces.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Lemma 3.5, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- A contraction of a standard Gaussian becomes standard Gaussian after adding an independent
standard Gaussian transformed by its defect operator. -/
theorem map_add_defect_stdGaussian (D : F →L[ℝ] E) (hD : ‖D‖ ≤ 1) :
    ((stdGaussian F).prod (stdGaussian E)).map
      (D.comp (.fst ℝ F E) + (CFC.sqrt (1 - D ∘L D.adjoint)).comp (.snd ℝ F E)) =
      stdGaussian E := by
  have hdefect : 0 ≤ (1 : E →L[ℝ] E) - D ∘L D.adjoint :=
    sub_nonneg.mpr (D.self_comp_adjoint_le_one hD)
  let S : E →L[ℝ] E := CFC.sqrt (1 - D ∘L D.adjoint)
  have hS : IsSelfAdjoint S :=
    (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg (1 - D ∘L D.adjoint))).isSelfAdjoint
  have hSq (z : E) : ‖D.adjoint z‖ ^ 2 + ‖S z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (S z),
      inner_sqrt_apply_sqrt_apply_eq_inner hdefect]
    simp only [sub_apply, one_apply_eq_self, inner_sub_left, comp_apply,
      ← D.adjoint_inner_right, real_inner_self_eq_norm_sq]
    ring
  apply Measure.ext_of_charFun
  funext z
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_map, charFunDual_prod,
    charFun_eq_charFunDual_toDualMap]
  have hinl : ((InnerProductSpace.toDualMap ℝ E z).comp
      (D.comp (.fst ℝ F E) + S.comp (.snd ℝ F E))).comp (.inl ℝ F E) =
      innerSL ℝ (D.adjoint z) := by
    ext w
    simp [InnerProductSpace.toDualMap_apply_apply, adjoint_inner_left]
  have hinr : ((InnerProductSpace.toDualMap ℝ E z).comp
      (D.comp (.fst ℝ F E) + S.comp (.snd ℝ F E))).comp (.inr ℝ F E) =
      innerSL ℝ (S z) := by
    ext w
    simp only [comp_apply, add_apply, inr_apply, map_zero, zero_add,
      InnerProductSpace.toDualMap_apply_apply, innerSL_apply_apply, coe_snd', coe_fst']
    exact (hS.isSymmetric z w).symm
  rw [hinl, hinr, charFunDual_stdGaussian, charFunDual_stdGaussian,
    charFunDual_stdGaussian, ← Complex.exp_add]
  simp only [innerSL_apply_norm, LinearIsometry.norm_map]
  congr 1
  norm_cast
  linarith [hSq z]

end ContinuousLinearMap
