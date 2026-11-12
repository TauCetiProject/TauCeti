/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of finite mixtures

A finite mixture has support equal to the union of its positive-weight component supports.
Zero-weight components contribute nothing. Finiteness makes this union closed, so no closure
is needed, unlike for general infinite mixtures. The component measures need not be probability
measures, and no compatibility of the topology with the measurable structure is required.
-/

public section

open Convexity MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- The support of a finite mixture is the union of the positive-weight component supports. -/
@[simp]
theorem support_finiteMixtureMeasure {I X : Type*} [Fintype I]
    [TopologicalSpace X] [MeasurableSpace X]
    (p : StdSimplex ℝ≥0 I) (K : I → Measure X) :
    (finiteMixtureMeasure p K).support = ⋃ i, ⋃ (_ : 0 < p.weights i), (K i).support := by
  classical
  rw [finiteMixtureMeasure_def, Measure.support_finset_sum]
  congr 1
  funext i
  by_cases hi : p.weights i = 0
  · simp [hi]
  · rw [Measure.support_smul_measure _ _ (by exact_mod_cast hi)]
    simp [pos_iff_ne_zero.mpr hi]

end TauCeti.Probability
