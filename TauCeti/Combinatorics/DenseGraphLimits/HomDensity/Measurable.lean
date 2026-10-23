/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Homomorphism densities of a measurable family of graphons

If a family of graphons `W t` depends jointly measurably on a parameter `t`, meaning that
`(t, x, y) ↦ W t x y` is measurable, then each homomorphism density `t ↦ t(F, W t)` is a
measurable parametric integral.

## Main results

* `TauCeti.DenseGraphLimits.measurable_homDensity` — the homomorphism density of a jointly
  measurable family of graphons is measurable in the parameter.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T : Type*} [MeasurableSpace T]

/-- **Homomorphism densities of a measurable family of graphons.** If a family of graphons depends
jointly measurably on a parameter, then so does the homomorphism density of every finite graph in
it. -/
theorem measurable_homDensity {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {W : T → Graphon Ω μ} (hW : Measurable fun p : T × Ω × Ω => W p.1 p.2.1 p.2.2) :
    Measurable fun t => homDensity F (W t) := by
  simp_rw [homDensity_def]
  refine (StronglyMeasurable.integral_prod_right'
    (f := fun p : T × (V → Ω) => ∏ e ∈ F.edgeFinset, edgeFactor (W p.1) p.2 e) ?_).measurable
  refine (Finset.measurable_prod _ fun e _ => ?_).stronglyMeasurable
  induction e using Sym2.ind with
  | _ a b =>
    simp only [edgeFactor_mk]
    exact hW.comp (f := fun p : T × (V → Ω) => (p.1, p.2 a, p.2 b)) (by fun_prop)

end DenseGraphLimits

end TauCeti
