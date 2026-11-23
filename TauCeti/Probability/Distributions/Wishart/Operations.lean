/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.Probability.Distributions.Wishart.Nonsingular

import TauCeti.Probability.Distributions.Wishart.CharFun
import TauCeti.Probability.Distributions.Wishart.Marginal

/-!
# Random-variable operations for nonsingular Wishart laws

This file gives the native random-variable forms of two fundamental operations on nonsingular
Wishart laws. Congruence transports the scale by the same congruence, and the sum of independent
matrices with a common scale adds their degrees.

The rectangular congruence theorems retain the hypotheses of their measure-level forms. A
rectangular projection can turn an invalid scale into a valid one, and a rank-deficient image of
a nonsingular law generally leaves the density family. Invertible nonsingular congruence is
available without parameter hypotheses because the source and target laws are zero together
outside the valid range.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Chapter 3.
-/

public section

noncomputable section

open MeasureTheory
open scoped Matrix MatrixOrder

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- The sum of independent nonsingular Wishart matrices with a common scale has the sum of their
real degrees. The output degree condition is needed in dimension zero, where two valid degrees
need not have a valid sum. The probability source and the two `HasLaw` hypotheses force the input
degrees and common scale to be valid. -/
theorem hasLaw_add_nonsingularWishartMeasure {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    {n₁ n₂ : ℝ} {S : Matrix (Fin p) (Fin p) ℝ} (hXY : IndepFun X Y P)
    (hX : HasLaw X (nonsingularWishartMeasure n₁ S) P)
    (hY : HasLaw Y (nonsingularWishartMeasure n₂ S) P)
    (hn : (p : ℝ) - 1 < n₁ + n₂) :
    HasLaw (X + Y) (nonsingularWishartMeasure (n₁ + n₂) S) P := by
  obtain ⟨hS, hn₁⟩ := isProbabilityMeasure_nonsingularWishartMeasure_iff.mp
    (hX.isProbabilityMeasure_iff.mp inferInstance)
  obtain ⟨-, hn₂⟩ := isProbabilityMeasure_nonsingularWishartMeasure_iff.mp
    (hY.isProbabilityMeasure_iff.mp inferInstance)
  let _ := isProbabilityMeasure_nonsingularWishartMeasure hS hn₁
  let _ := isProbabilityMeasure_nonsingularWishartMeasure hS hn₂
  rw [← nonsingularWishartMeasure_conv_nonsingularWishartMeasure S hn₁ hn₂ hn]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory.IndepFun

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Invertible congruence sends a nonsingular Wishart random matrix to the law whose scale is
transformed by the same congruence. This also covers every invalid parameter, where both laws are
zero. -/
theorem symmetricCongruence_nonsingularWishartMeasure {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hW : HasLaw W (nonsingularWishartMeasure n S) P)
    (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    HasLaw (fun ω ↦ Matrix.GeneralLinearGroup.symmetricCongruence C (W ω))
      (nonsingularWishartMeasure n
        ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ)) P := by
  have hmap : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hlaw := (hasLaw_map hmap.aemeasurable).comp hW
  rwa [map_symmetricCongruence_nonsingularWishartMeasure n S C] at hlaw

/-- Full-row-rank rectangular congruence sends a nonsingular Wishart random matrix to the
nonsingular law whose scale is transformed by the same congruence. -/
theorem symmetricCongruenceLinearMap_nonsingularWishartMeasure {p q : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hW : HasLaw W (nonsingularWishartMeasure n S) P)
    (M : Matrix (Fin q) (Fin p) ℝ) (hM : M.rank = q) (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) :
    HasLaw (fun ω ↦ Matrix.symmetricCongruenceLinearMap M (W ω))
      (nonsingularWishartMeasure n (M * S * Mᵀ)) P := by
  have hmap : Measurable (Matrix.symmetricCongruenceLinearMap M) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hlaw := (hasLaw_map hmap.aemeasurable).comp hW
  rwa [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure M hM hS hn] at hlaw

end ProbabilityTheory.HasLaw
