/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

/-- **The Dirichlet family is measurable in its concentration vector.** -/
@[fun_prop]
theorem measurable_dirichletMeasure :
    Measurable fun a : ι → ℝ ↦ dirichletMeasure a := by
  classical
  have hformula : (fun a : ι → ℝ ↦ dirichletMeasure a) = fun a ↦
      if Nonempty ι ∧ ∀ i, 0 < a i then
        (Measure.pi fun i ↦ gammaMeasure (a i) 1).map dirichletNormalize else 0 := by
    funext a
    split_ifs with ha
    · let _ : Nonempty ι := ha.1
      exact dirichletMeasure_of_pos ha.2
    · exact dirichletMeasure_eq_zero_of_invalid ha
  rw [hformula]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact MeasurableSet.inter (MeasurableSet.const (Nonempty ι))
      (measurableSet_setOfPred.2 <| .forall fun i ↦
        measurableSet_setOfPred.1 <| measurableSet_lt measurable_const (measurable_pi_apply i))
  · simp_rw [pi_gammaMeasure_eq_withDensity]
    refine (Measure.measurable_map dirichletNormalize measurable_dirichletNormalize).comp
      (measurable_withDensity ?_)
    refine Finset.measurable_prod _ fun i _ ↦ ?_
    have hcoord : Measurable
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ ((q.1 i, (1 : ℝ)), q.2 i)) := by fun_prop
    exact measurable_uncurry_gammaPDF.comp hcoord

end Probability

end TauCeti
