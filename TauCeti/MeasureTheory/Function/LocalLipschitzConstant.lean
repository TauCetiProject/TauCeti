/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.Topology.EMetricSpace.LocalLipschitzConstant

/-!
# Measurability of the local Lipschitz constant

The local Lipschitz constant `TauCeti.localLipschitzConstant f` of a continuous map `f` is a
countable infimum of lower semicontinuous functions, hence a Borel function. This is what makes
integrals such as `∫ |D u|² dm`, which enter the Cheeger energy of a metric-measure space, additive
in the integrand.

## Main results

* `Continuous.measurable_localLipschitzConstant`: the local Lipschitz constant of a continuous map
  is Borel.
-/

public section

open MeasureTheory

namespace TauCeti

variable {X Y : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [PseudoEMetricSpace Y]

/-- The local Lipschitz constant of a continuous map into an extended pseudometric space is a Borel
function. -/
theorem _root_.Continuous.measurable_localLipschitzConstant [OpensMeasurableSpace X] {f : X → Y}
    (hf : Continuous f) : Measurable (localLipschitzConstant f) := by
  have h : localLipschitzConstant f = _ := funext fun x ↦
    localLipschitzConstant_eq_iInf_iSup (x := x) fun y hy ↦
      ((EMetric.inseparable_iff.2 hy).map hf).edist_eq_zero
  rw [h]
  exact Measurable.iInf fun n ↦ (hf.lowerSemicontinuous_iSup_edist_div _).measurable

end TauCeti
