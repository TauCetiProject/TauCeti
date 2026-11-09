/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.MeasureTheory.Measure.AddCircle

/-!
# Uniform interval laws and Haar-uniform angles

Reading a Haar-uniform circle point in any half-open chart gives the uniform interval law.
Conversely, reducing a uniform interval of length one period modulo that period gives Haar
probability. Although the chart uses `[a, a + T)` and `uniformMeasure` uses `(a, a + T]`, the
endpoint difference is Lebesgue-null.

In particular, the representative of a Haar-uniform angle in `[-π, π)` has law
`uniformMeasure (-π) π`. The general transport identities also give random-variable versions
for arbitrary source measures, without an extra probability assumption on the source.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Reading Haar probability in the chart `[a, a + T)` gives the uniform interval law. -/
theorem map_coe_equivIco_haarAddCircle (a : ℝ) :
    (AddCircle.haarAddCircle : Measure (AddCircle T)).map
        (fun θ ↦ (AddCircle.equivIco T a θ : ℝ)) = uniformMeasure a (a + T) := by
  have h := AddCircle.map_coe_equivIco_withDensity_haarAddCircle (T := T) a
    (f := fun _ ↦ 1) measurable_const
  simpa [uniformMeasure_eq_smul, Measure.restrict_congr_set Ico_ae_eq_Ioc,
    withDensity_const] using h

/-- Reducing a uniform interval of length `T` modulo `T` gives Haar probability. -/
theorem map_coe_uniformMeasure (a : ℝ) :
    (uniformMeasure a (a + T)).map ((↑) : ℝ → AddCircle T) =
      AddCircle.haarAddCircle := by
  have hm : Measurable fun θ : AddCircle T ↦ (AddCircle.equivIco T a θ : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco T a).measurable
  rw [← map_coe_equivIco_haarAddCircle (T := T) a,
    Measure.map_map AddCircle.measurable_mk' hm]
  simp [Function.comp_def]

local instance uniformAddCirclePeriodPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The Haar-uniform angle representative in `[-π, π)` has the uniform law on `(-π, π]`.
The two choices at the seam do not change the real measure. -/
theorem map_angle_haarAddCircle :
    (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))).map
        (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) = uniformMeasure (-π) π := by
  have hπ : -π + 2 * π = π := by ring
  simpa only [hπ] using map_coe_equivIco_haarAddCircle (T := 2 * π) (-π)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {T : ℝ} [Fact (0 < T)] {a : ℝ}

/-- The representative in any chart of a Haar-uniform random circle point is uniform. -/
theorem HasLaw.equivIco_haarAddCircle {X : Ω → AddCircle T}
    (hX : HasLaw X AddCircle.haarAddCircle P) (a : ℝ) :
    HasLaw (fun ω ↦ (AddCircle.equivIco T a (X ω) : ℝ)) (uniformMeasure a (a + T)) P := by
  rw [← map_coe_equivIco_haarAddCircle (T := T) a]
  exact (hasLaw_map (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco T a).measurable).aemeasurable).comp hX

/-- Reducing an interval-uniform random variable modulo its interval length is Haar-uniform. -/
theorem HasLaw.coe_uniformMeasure {X : Ω → ℝ}
    (hX : HasLaw X (uniformMeasure a (a + T)) P) :
    HasLaw (fun ω ↦ (X ω : AddCircle T)) AddCircle.haarAddCircle P := by
  rw [← map_coe_uniformMeasure (T := T) a]
  exact (hasLaw_map AddCircle.measurable_mk'.aemeasurable).comp hX

end ProbabilityTheory
