/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The `Lᵖ` seminorm of a displacement is that of the distance

On a seminormed additive group `E` the extended distance is the extended norm of the difference,
`edist x y = ‖x - y‖ₑ`. So under any measure `π` on `E × E` the displacement `(x, y) ↦ x - y` and
the ground distance `(x, y) ↦ edist x y` have the same `Lᵖ` seminorm
(`MeasureTheory.eLpNorm_sub_eq_eLpNorm_edist`). This turns an `Lᵖ` cost written with `edist`, as
in optimal transport, into the `Lᵖ` seminorm of an `E`-valued function, to which the linear
structure of `E` applies (for instance, scaling by a constant).

The measurability assumptions on `E` make both functions almost everywhere strongly measurable,
which `MeasureTheory.eLpNorm_congr_enorm_ae` needs.

On a pseudometric space, `MeasureTheory.memLp_dist_iff_memLp_edist` likewise identifies membership
in `Lᵖ` of the real distance to a basepoint with that of the extended distance.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- Under any law `π` on pairs of points of a seminormed group, the displacement `x - y` and the
ground distance `edist x y` have the same `Lᵖ` seminorm. -/
theorem eLpNorm_sub_eq_eLpNorm_edist {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] (p : ℝ≥0∞) (π : Measure (E × E)) :
    eLpNorm (fun z : E × E ↦ z.1 - z.2) p π = eLpNorm (fun z : E × E ↦ edist z.1 z.2) p π :=
  eLpNorm_congr_enorm_ae (by fun_prop) measurable_edist.aestronglyMeasurable
    (.of_forall fun z ↦ by simp [edist_eq_enorm_sub])

/-- On a pseudometric space, the real-distance and extended-distance formulations of
finite `p`-moment at a basepoint agree. -/
theorem memLp_dist_iff_memLp_edist {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {p : ℝ≥0∞} {x : X} {ν : Measure X} :
    MemLp (fun y ↦ dist y x) p ν ↔ MemLp (fun y ↦ edist x y) p ν := by
  have key (hd : AEStronglyMeasurable (fun y ↦ dist y x) ν) :
      MemLp (fun y ↦ dist y x) p ν ↔ MemLp (fun y ↦ edist x y) p ν := by
    apply memLp_congr_enorm
    · exact hd
    · exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable hd).congr
        (.of_forall fun y ↦ by simp only [edist_dist, dist_comm])
    · exact .of_forall fun y ↦ by
        simp only [edist_dist, dist_comm, enorm_eq_self]
        exact Real.enorm_eq_ofReal dist_nonneg
  refine ⟨fun h ↦ (key h.aestronglyMeasurable).1 h, fun h ↦ (key ?_).2 h⟩
  exact h.aestronglyMeasurable.aemeasurable.ennreal_toReal.aestronglyMeasurable.congr
    (.of_forall fun y ↦ by simp only [← dist_edist, dist_comm])

end MeasureTheory
