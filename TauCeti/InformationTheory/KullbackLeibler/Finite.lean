/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Relative entropy on a finite measurable space

For finite measures on a finite type, a reference measure that charges every singleton
dominates every measure. Its Kullback–Leibler divergence is the finite sum of the
`klFun` values of the ratios of singleton masses. This formula connects the
measure-theoretic entropy to finite matrix objectives, including the finite
Schrödinger problem and Sinkhorn scaling.

Mathlib's `InformationTheory.klDiv` includes the finite-measure mass correction; the
formula here uses its `klFun` representation, so it remains valid when the two total
masses differ. The Radon–Nikodym derivative at each atom is provided by
`MeasureTheory.Measure.rnDeriv_eq_measure_singleton_div`.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

/-- On a finite space with a full-support finite reference measure, relative entropy is the
finite sum of the `klFun` values of the ratios of singleton masses, weighted by the
reference masses. This includes the mass correction for unequal total masses. -/
theorem klDiv_eq_sum_klFun_singleton [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ∀ x : α, ν {x} ≠ 0) :
    klDiv μ ν = ∑ x : α,
      ENNReal.ofReal (klFun ((μ {x} / ν {x}).toReal)) * ν {x} := by
  rw [klDiv_eq_lintegral_klFun_of_ac
    (absolutelyContinuous_of_forall_singleton_ne_zero hν),
    lintegral_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Measure.rnDeriv_eq_measure_singleton_div (hν x) (measure_ne_top ν _)]

/-- The log-ratio form of finite relative entropy. The last two terms are Mathlib's
finite-measure mass correction, and cancel when the measures have the same mass. -/
theorem klDiv_eq_ofReal_sum_log_singleton [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ∀ x : α, ν {x} ≠ 0) :
    klDiv μ ν = ENNReal.ofReal
      ((∑ x : α, μ.real {x} * Real.log (μ.real {x} / ν.real {x})) +
        ν.real Set.univ - μ.real Set.univ) := by
  have hac : μ ≪ ν := absolutelyContinuous_of_forall_singleton_ne_zero hν
  rw [klDiv_of_ac_of_integrable hac (Integrable.of_finite),
    integral_fintype (f := llr μ ν) (μ := μ) (Integrable.of_finite)]
  have hsum : (∑ x : α, μ.real {x} • llr μ ν x) =
      ∑ x : α, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [smul_eq_mul, llr]
    rw [Measure.rnDeriv_eq_measure_singleton_div (hν x) (measure_ne_top ν _),
      ENNReal.toReal_div]
    rfl
  rw [hsum]

end TauCeti
