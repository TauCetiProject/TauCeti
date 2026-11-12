/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.Data.Matrix.Scaling.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Basic
public import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous

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

namespace MeasureTheory.Measure

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- For finite measures on a finite product, KL divergence is matrix entropy plus Mathlib's
finite-measure mass correction when the first measure vanishes at every zero of the reference.
The measures are encoded by their singleton masses; no separate nonnegativity assumption on
`P` or `K` is needed. -/
theorem klDiv_eq_ofReal_relEntropy_add_mass_correction_of_real_singleton
    (π R : Measure (ι × κ)) [IsFiniteMeasure π] [IsFiniteMeasure R]
    (P K : Matrix ι κ ℝ)
    (hπ : ∀ i j, π.real {(i, j)} = P i j)
    (hR : ∀ i j, R.real {(i, j)} = K i j)
    (hPK : ∀ i j, K i j = 0 → P i j = 0) :
    klDiv π R = ENNReal.ofReal
      (Matrix.relEntropy P K + R.real Set.univ - π.real Set.univ) := by
  have hac : π ≪ R := by
    refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
    rw [← Set.Finite.coe_toFinset (Set.toFinite s), ← sum_measure_singleton]
    apply Finset.sum_eq_zero
    intro q hq
    have hRq : R {q} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr ((Set.toFinite s).mem_toFinset.mp hq)) hs
    have hKq : K q.1 q.2 = 0 := by
      rw [← hR q.1 q.2, Measure.real, hRq]
      simp
    have hPq := hPK q.1 q.2 hKq
    rw [← hπ q.1 q.2, Measure.real] at hPq
    exact ((ENNReal.toReal_eq_zero_iff _).mp hPq).resolve_right (measure_ne_top _ _)
  rw [klDiv_of_ac_of_integrable hac Integrable.of_finite,
    integral_fintype (f := llr π R) (μ := π) (Integrable.of_finite)]
  have hsum :
      (∑ q : ι × κ, π.real {q} • llr π R q) =
        Matrix.relEntropy P K := by
    rw [Matrix.relEntropy_def, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hK : K i j = 0
    · simp [hπ i j, hPK i j hK]
    · have hRne : R {(i, j)} ≠ 0 := by
        intro hzero
        apply hK
        rw [← hR i j, Measure.real, hzero]
        simp
      simp only [smul_eq_mul]
      rw [llr_eq_log_real_div_real_singleton π R (i, j) hRne (measure_ne_top R _),
        hπ i j, hR i j]
      by_cases hP : P i j = 0
      · simp [hP]
      · rw [Real.log_div hP hK]
        ring
  rw [hsum]

end MeasureTheory.Measure
