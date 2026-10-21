/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.StdSimplex
import TauCeti.Probability.Distributions.Gamma.Measurability

/-!
# Parameter measurability of the Dirichlet distribution

The Dirichlet law depends measurably on its concentration vector.  Thus a measurable random
concentration vector can be composed with `dirichletMeasure` to give a measure-valued kernel.
The coordinate vector can also be read as a nonnegative simplex parameter almost surely,
using a measurable extension of the inverse weight map for subsequent mixtures.

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

open scoped NNReal in
/-- Reading a Dirichlet vector through a simplex-weight extension preserves its coordinates
almost surely, independently of the chosen fallback point. -/
theorem ae_extendWeights_dirichletMeasure [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (p : Convexity.StdSimplex ℝ≥0 ι) :
    ∀ᵐ x ∂dirichletMeasure a, ∀ i,
      ((p.extendWeights (fun j ↦ (x j).toNNReal)).weights i : ℝ) = x i := by
  classical
  filter_upwards [ae_pos_dirichletMeasure ha, ae_sum_eq_one_dirichletMeasure ha] with x hx hsum
  have hw : (fun i ↦ (x i).toNNReal) ∈
      Set.range (fun q : Convexity.StdSimplex ℝ≥0 ι ↦ (q.weights : ι → ℝ≥0)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    refine ⟨by simp, ?_⟩
    apply NNReal.coe_injective
    simpa [Real.toNNReal_of_nonneg (hx _).le] using hsum
  intro i
  have hp := congrFun (p.weights_extendWeights_of_mem_range hw) i
  rw [hp]
  exact Real.coe_toNNReal _ (hx i).le

end Probability

end TauCeti
