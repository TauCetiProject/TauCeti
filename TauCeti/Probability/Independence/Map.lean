/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence under a pushforward

Two functions are independent under the pushforward of a measure along a measurable map exactly
when their composites with that map are independent under the measure. Both sides are the
product identity for the joint law, and the pushforward moves through that identity.

## Main results

* `ProbabilityTheory.indepFun_map_iff_comp`
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
  [MeasurableSpace γ] {μ : Measure Ω}

/-- Independence of two functions under a pushforward is independence of their composites. -/
theorem indepFun_map_iff_comp [IsProbabilityMeasure μ] {m : Ω → Ω'} (hm : Measurable m)
    {f : Ω' → β} {g : Ω' → γ} (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g (μ.map m) ↔ IndepFun (f ∘ m) (g ∘ m) μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map' hf.aemeasurable hg.aemeasurable inferInstance
      inferInstance,
    indepFun_iff_map_prod_eq_prod_map_map' (hf.comp hm).aemeasurable (hg.comp hm).aemeasurable
      inferInstance inferInstance,
    Measure.map_map (hf.prodMk hg) hm, Measure.map_map hf hm, Measure.map_map hg hm]
  rfl

end ProbabilityTheory
