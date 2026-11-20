/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Measurability of the map of a matrix field on Euclidean space

`Matrix.toEuclideanCLM` is a homeomorphism between square matrices and the continuous linear
maps of Euclidean space (`Matrix.continuous_toEuclideanCLM`,
`Matrix.continuous_toEuclideanCLM_symm`), so a field of matrices is a.e. strongly measurable
exactly when the field of their operators is (`Matrix.aestronglyMeasurable_toEuclideanCLM_iff`).
-/

public section

namespace Matrix

open MeasureTheory

/-- A field of matrices is a.e. strongly measurable exactly when the field of the operators they
define on Euclidean space is. -/
theorem aestronglyMeasurable_toEuclideanCLM_iff {𝕜 ι X : Type*} [RCLike 𝕜] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι 𝕜} :
    AEStronglyMeasurable (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ ↔
      AEStronglyMeasurable a μ :=
  ⟨fun h => by
    simpa only [StarAlgEquiv.symm_apply_apply] using
      continuous_toEuclideanCLM_symm.comp_aestronglyMeasurable h,
    fun h => continuous_toEuclideanCLM.comp_aestronglyMeasurable h⟩

end Matrix
