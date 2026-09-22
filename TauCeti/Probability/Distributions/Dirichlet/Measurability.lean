/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.Distributions.Dirichlet.Basic
import TauCeti.Probability.Distributions.Gamma.Measurability

/-!
# Parameter measurability of the Dirichlet distribution

The Dirichlet law depends measurably on its concentration vector.  Thus a measurable random
concentration vector can be composed with `dirichletMeasure` to give a measure-valued kernel.

The result covers the totalized family: the measure is zero when the coordinate type is empty or a
concentration parameter is nonpositive, while on the valid region it is the normalized image of a
finite product of Gamma laws.

## Main result

* `TauCeti.Probability.measurable_dirichletMeasure` gives joint measurability in every
  concentration coordinate.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- An everywhere-probability extension of the unit-rate Gamma family. -/
private def validGammaMeasure (a : ℝ) : Measure ℝ :=
  if 0 < a then gammaMeasure a 1 else Measure.dirac 0

private theorem isProbabilityMeasure_validGammaMeasure (a : ℝ) :
    IsProbabilityMeasure (validGammaMeasure a) := by
  rw [validGammaMeasure]
  split_ifs with ha
  · exact isProbabilityMeasure_gammaMeasure ha one_pos
  · infer_instance

private theorem measurable_validGammaMeasure : Measurable validGammaMeasure := by
  unfold validGammaMeasure
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  fun_prop

private def gammaProbability (a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨validGammaMeasure a, isProbabilityMeasure_validGammaMeasure a⟩

private theorem measurable_gammaProbability : Measurable gammaProbability := by
  exact measurable_validGammaMeasure.subtype_mk

private def dirichletSource (a : ι → ℝ) : Measure (ι → ℝ) :=
  (ProbabilityMeasure.pi fun i ↦ gammaProbability (a i)).toMeasure

private theorem measurable_dirichletSource : Measurable (dirichletSource (ι := ι)) := by
  exact TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_toMeasure
    (Ω := ι → ℝ) (ι := ι) (α := fun _ ↦ ℝ) (fun i a ↦ gammaProbability (a i))
    fun i ↦ measurable_gammaProbability.comp (measurable_pi_apply i)

private theorem dirichletSource_of_pos {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    dirichletSource a = Measure.pi fun i ↦ gammaMeasure (a i) 1 := by
  rw [dirichletSource, ProbabilityMeasure.toMeasure_pi]
  congr 1
  funext i
  simp [gammaProbability, validGammaMeasure, ha i]

/-- **The Dirichlet family is measurable in its concentration vector.** -/
@[fun_prop]
theorem measurable_dirichletMeasure :
    Measurable fun a : ι → ℝ ↦ dirichletMeasure a := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hzero : (fun a : ι → ℝ ↦ dirichletMeasure a) = fun _ ↦ 0 := by
      funext a
      exact dirichletMeasure_eq_zero_of_invalid fun h ↦ (not_nonempty_iff.mpr hι) h.1
    rw [hzero]
    exact measurable_const
  let _ : Nonempty ι := hι
  have hformula : (fun a : ι → ℝ ↦ dirichletMeasure a) = fun a ↦
      if ∀ i, 0 < a i then (dirichletSource a).map dirichletNormalize else 0 := by
    funext a
    by_cases ha : ∀ i, 0 < a i
    · rw [dirichletMeasure_of_pos ha, ite_eq_left ha]
      rw [dirichletSource_of_pos ha]
    · rw [dirichletMeasure_eq_zero_of_invalid (by simp [ha]), ite_eq_right ha]
  rw [hformula]
  have hpos : MeasurableSet {a : ι → ℝ | ∀ i, 0 < a i} :=
    measurableSet_setOfPred.2 <| .forall fun i ↦
      measurableSet_setOfPred.1 <| measurableSet_lt measurable_const (measurable_pi_apply i)
  exact Measurable.ite hpos
    ((Measure.measurable_map dirichletNormalize measurable_dirichletNormalize).comp
      measurable_dirichletSource)
    measurable_const

end Probability

end TauCeti
