/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import Mathlib.Probability.Kernel.Composition.MapComap
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
import TauCeti.MeasureTheory.Measure.TotalVariation.Coupling

/-!
# Total variation of mixtures of kernel rows

Averaging two kernels against the same finite measure bounds the total variation distance of
the mixtures by the corresponding weighted sum of row distances. Applying this to an optimal
coupling of two initial measures gives a contraction bound with the largest row distance as
the factor, using half of Mathlib's total variation distance for that factor.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.7 and Lemma 4.11.
-/

public section

open ProbabilityTheory Set
open scoped BigOperators

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- On a finite discrete source, the real mass of a measurable event after applying a finite
kernel is the sum of its masses under the rows, weighted by the initial singleton masses. -/
theorem measureReal_comp_apply_eq_sum [Fintype α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsFiniteKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∑ x, μ.real {x} * (κ x).real s := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable, lintegral_fintype,
    ENNReal.toReal_sum (fun _ _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [measureReal_def, measureReal_def, ENNReal.toReal_mul, mul_comm]

variable [MeasurableSingletonClass α]

/-- The total variation distance of two mixtures with the same weights is at most the
weighted sum of the total variation distances of their components. -/
theorem tvDist_comp_le_sum [Fintype α] (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    tvDist (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ∑ x, μ.real {x} * tvDist (κ x) (η x) := by
  classical
  rw [tvDist_eq_iSup_finPartition_abs]
  refine Real.iSup_le (fun P ↦ ?_)
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg tvDist_nonneg)
  simp only [measureReal_comp_apply_eq_sum _ _ (Subtype.property _)]
  calc
    _ = ∑ p ∈ P.parts, |∑ x, μ.real {x} * ((κ x).real p - (η x).real p)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ P.parts, ∑ x, μ.real {x} * |(κ x).real p - (η x).real p| := by
      apply Finset.sum_le_sum
      intro p _
      simpa [abs_mul, abs_of_nonneg measureReal_nonneg] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun x ↦ μ.real {x} * ((κ x).real p - (η x).real p))
    _ ≤ _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      apply Finset.sum_le_sum
      exact fun x _ ↦ mul_le_mul_of_nonneg_left
        (sum_abs_measureReal_sub_le_tvDist P) measureReal_nonneg

/-- On a finite discrete source, a finite kernel contracts the total variation distance between
finite measures of equal mass by a factor `c` if the distance between every pair of rows is at
most `2 * c`. -/
theorem tvDist_comp_le_mul [Finite α] (μ : Measure α) (κ : Kernel α β) [IsFiniteKernel κ]
    {ν : Measure α} [IsFiniteMeasure μ] (hmass : μ univ = ν univ)
    {c : ℝ} (h : ∀ x y, tvDist (κ x) (κ y) ≤ 2 * c) :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ c * tvDist μ ν := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨γ, hγ, hopt⟩ := TauCeti.isLeast_measureReal_ne_of_isCoupling hmass |>.1
  have : IsFiniteMeasure γ := hγ.isFiniteMeasure
  have hne : γ.real {z | z.1 ≠ z.2} = tvDist μ ν / 2 := hopt
  have hmix := γ.tvDist_comp_le_sum (κ.comap Prod.fst measurable_fst)
    (κ.comap Prod.snd measurable_snd)
  simp only [Kernel.coe_comap, Function.comp_def] at hmix
  rw [← Measure.bind_map measurable_fst.aemeasurable κ.aemeasurable,
    ← Measure.bind_map measurable_snd.aemeasurable κ.aemeasurable] at hmix
  rw [← Measure.fst, ← Measure.snd, hγ.fst_eq, hγ.snd_eq] at hmix
  refine hmix.trans ?_
  calc
    _ ≤ ∑ z ∈ Finset.univ.filter (fun z : α × α ↦ z.1 ≠ z.2), γ.real {z} * (2 * c) := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : z.1 = z.2
      · simp [hz, tvDist_self]
      · simp only [hz, ne_eq, not_false_eq_true, ite_true]
        exact mul_le_mul_of_nonneg_left (h _ _) measureReal_nonneg
    _ = c * tvDist μ ν := by
      rw [← Finset.sum_mul, sum_measureReal_singleton]
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      -- Optimality identifies the off-diagonal mass with half of the initial distance.
      rw [hne]
      ring

end MeasureTheory.Measure
