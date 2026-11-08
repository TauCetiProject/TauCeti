/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `Lᵖ` seminorm of a displacement is that of the distance

On a seminormed additive group `E` the extended distance is the extended norm of the difference,
`edist x y = ‖x - y‖ₑ`. So under any measure `π` on `E × E` the displacement `(x, y) ↦ x - y` and
the ground distance `(x, y) ↦ edist x y` have the same `Lᵖ` seminorm
(`MeasureTheory.eLpNorm_sub_eq_eLpNorm_edist`). This turns an `Lᵖ` cost written with `edist`, as
in optimal transport, into the `Lᵖ` seminorm of an `E`-valued function, to which the linear
structure of `E` applies (for instance, scaling by a constant).

The Minkowski estimate `MeasureTheory.eLpNorm_edist_comp_prod_le` bounds the `Lᵖ` seminorm of
the distance between the images of the two coordinates under maps `Q₁`, `Q₂` by the seminorm of
the distance plus the two displacements `edist z.1 (Q₁ z.1)` and `edist z.2 (Q₂ z.2)`.

The measurability assumptions on `E` make both functions almost everywhere strongly measurable,
which `MeasureTheory.eLpNorm_congr_enorm_ae` needs.
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

/-- **Minkowski bound for quantized distances.** The `L^p (γ)` norm of the distance between the
quantized points `Q₁ z.1` and `Q₂ z.2` is at most the `L^p (γ)` norm of the distance `d (z.1, z.2)`
plus the two displacement norms `d (z.1, Q₁ z.1)` and `d (z.2, Q₂ z.2)`. -/
theorem eLpNorm_edist_comp_prod_le {Y : Type*} [MeasurableSpace Y] [PseudoEMetricSpace Y]
    {p : ℝ≥0∞} {Q₁ Q₂ : Y → Y} (hp1 : 1 ≤ p) (γ : Measure (Y × Y))
    (hmeas : AEStronglyMeasurable (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) γ) :
    eLpNorm (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) p γ ≤
      eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p γ +
        (eLpNorm (fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) p γ +
          eLpNorm (fun z : Y × Y ↦ edist z.2 (Q₂ z.2)) p γ) := by
  calc eLpNorm (fun z : Y × Y ↦ edist (Q₁ z.1) (Q₂ z.2)) p γ
      ≤ eLpNorm ((fun z : Y × Y ↦ edist z.1 z.2) +
          ((fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) + fun z ↦ edist z.2 (Q₂ z.2))) p γ := by
        refine eLpNorm_mono_enorm hmeas fun z ↦ ?_
        simp only [enorm_eq_self, Pi.add_apply]
        calc edist (Q₁ z.1) (Q₂ z.2)
            ≤ edist (Q₁ z.1) z.1 + edist z.1 z.2 + edist z.2 (Q₂ z.2) :=
              edist_triangle4 _ _ _ _
          _ = edist z.1 z.2 + (edist z.1 (Q₁ z.1) + edist z.2 (Q₂ z.2)) := by
              rw [edist_comm (Q₁ z.1)]
              ring
    _ ≤ eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p γ +
          (eLpNorm (fun z : Y × Y ↦ edist z.1 (Q₁ z.1)) p γ +
            eLpNorm (fun z : Y × Y ↦ edist z.2 (Q₂ z.2)) p γ) :=
        (eLpNorm_add_le hp1).trans (add_le_add le_rfl (eLpNorm_add_le hp1))

end MeasureTheory
