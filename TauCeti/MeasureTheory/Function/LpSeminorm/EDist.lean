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

The measurability assumptions on `E` make both functions almost everywhere strongly measurable,
which `MeasureTheory.eLpNorm_congr_eNorm_ae` needs.

On a pseudometric space, `MeasureTheory.memLp_dist_iff_memLp_edist` likewise identifies membership
in `Lᵖ` of the real distance to a basepoint with that of the extended distance.

The Minkowski estimate `MeasureTheory.eLpNorm_edist_le_add` bounds the `Lᵖ` seminorm of
`x ↦ edist (f' x) (g' x)` by that of `x ↦ edist (f x) (g x)` plus the seminorms of the two
displacements `x ↦ edist (f x) (f' x)` and `x ↦ edist (g x) (g' x)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- Under any law `π` on pairs of points of a seminormed group, the displacement `x - y` and the
ground distance `edist x y` have the same `Lᵖ` seminorm. -/
theorem eLpNorm_sub_eq_eLpNorm_edist {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] (p : ℝ≥0∞) (π : Measure (E × E)) :
    eLpNorm (fun z : E × E ↦ z.1 - z.2) p π = eLpNorm (fun z : E × E ↦ edist z.1 z.2) p π :=
  eLpNorm_congr_eNorm_ae (by fun_prop) measurable_edist.aestronglyMeasurable
    (.of_forall fun z ↦ by simp [eDist_eq_eNorm_sub])

/-- On a pseudometric space, the real-distance and extended-distance formulations of
finite `p`-moment at a basepoint agree. -/
theorem memLp_dist_iff_memLp_edist {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {p : ℝ≥0∞} {x : X} {ν : Measure X} :
    MemLp (fun y ↦ dist y x) p ν ↔ MemLp (fun y ↦ edist x y) p ν := by
  have key (hd : AEStronglyMeasurable (fun y ↦ dist y x) ν) :
      MemLp (fun y ↦ dist y x) p ν ↔ MemLp (fun y ↦ edist x y) p ν := by
    apply memLp_congr_eNorm
    · exact hd
    · exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable hd).congr
        (.of_forall fun y ↦ by simp only [edist_dist, dist_comm])
    · exact .of_forall fun y ↦ by
        simp only [edist_dist, dist_comm, eNorm_eq_self]
        exact Real.eNorm_eq_ofReal dist_nonneg
  refine ⟨fun h ↦ (key h.aestronglyMeasurable).1 h, fun h ↦ (key ?_).2 h⟩
  exact h.aestronglyMeasurable.aemeasurable.ennreal_toReal.aestronglyMeasurable.congr
    (.of_forall fun y ↦ by simp only [← dist_edist, dist_comm])

/-- **Minkowski bound for distances.** For maps `f g f' g' : α → Y` into a pseudo-emetric space
and `1 ≤ p`, the `Lᵖ(μ)` seminorm of `x ↦ edist (f' x) (g' x)` is at most that of
`x ↦ edist (f x) (g x)` plus those of the two displacements `x ↦ edist (f x) (f' x)` and
`x ↦ edist (g x) (g' x)`. -/
theorem eLpNorm_edist_le_add {α Y : Type*} {m : MeasurableSpace α} [PseudoEMetricSpace Y]
    {p : ℝ≥0∞} {μ : Measure α} {f g f' g' : α → Y} (hp1 : 1 ≤ p)
    (hmeas : AEStronglyMeasurable (fun x ↦ edist (f' x) (g' x)) μ) :
    eLpNorm (fun x ↦ edist (f' x) (g' x)) p μ ≤
      eLpNorm (fun x ↦ edist (f x) (g x)) p μ +
        (eLpNorm (fun x ↦ edist (f x) (f' x)) p μ + eLpNorm (fun x ↦ edist (g x) (g' x)) p μ) := by
  calc eLpNorm (fun x ↦ edist (f' x) (g' x)) p μ
      ≤ eLpNorm ((fun x ↦ edist (f x) (g x)) +
          ((fun x ↦ edist (f x) (f' x)) + fun x ↦ edist (g x) (g' x))) p μ := by
        refine eLpNorm_mono_eNorm hmeas fun x ↦ ?_
        simp only [eNorm_eq_self, Pi.add_apply]
        calc edist (f' x) (g' x)
            ≤ edist (f' x) (f x) + edist (f x) (g x) + edist (g x) (g' x) :=
              edist_triangle4 _ _ _ _
          _ = edist (f x) (g x) + (edist (f x) (f' x) + edist (g x) (g' x)) := by
              rw [edist_comm (f' x)]
              ring
    _ ≤ eLpNorm (fun x ↦ edist (f x) (g x)) p μ +
          (eLpNorm (fun x ↦ edist (f x) (f' x)) p μ + eLpNorm (fun x ↦ edist (g x) (g' x)) p μ) :=
        (eLpNorm_add_le hp1).trans (add_le_add le_rfl (eLpNorm_add_le hp1))

end MeasureTheory
