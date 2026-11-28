/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Int
public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Inversion for sums of independent integer random variables

The inversion formula on the integers,
`MeasureTheory.measureReal_singleton_eq_integral_charFun_map_intCast`, expresses the masses of an
integer law through its characteristic function. Since the characteristic function of a sum of
independent random variables is the product of those of the summands, the probability that a sum
`S = ∑ i ∈ s, X i` of independent integer random variables takes the value `k` is the `k`-th
Fourier coefficient of that product. For a sum `Sₙ = X 0 + ⋯ + X (n - 1)` of independent
identically distributed integer random variables it reads
`P(Sₙ = k) = (2π)⁻¹ ∫_{-π}^{π} exp(-i t k) φ(t)ⁿ dt`, with `φ` the characteristic function of
`X 0`: this is the starting point of the Fourier-analytic proof of the local limit theorem for
lattice laws.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_sum_eq_integral_prod_charFun`: inversion for a sum of
  independent integer random variables.
* `ProbabilityTheory.iIndepFun.measureReal_sum_range_eq_integral_charFun_pow`: inversion for a sum
  of independent identically distributed integer random variables.

## References

* R. Durrett, *Probability: Theory and Examples*, fifth edition, Exercise 3.3.2 (ii).
-/

public section

open Complex Real

namespace ProbabilityTheory

open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Inversion for a sum of independent integer random variables.** For independent
integer-valued `X i`, `i ∈ s`, the probability that `∑ i ∈ s, X i = k` is the `k`-th Fourier
coefficient of the product of the characteristic functions of the laws of the summands. -/
theorem iIndepFun.measureReal_sum_eq_integral_prod_charFun {X : ι → Ω → ℤ} {s : Finset ι}
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) (k : ℤ) :
    (P.real {ω | ∑ i ∈ s, X i ω = k} : ℂ) = (2 * π : ℂ)⁻¹ * ∫ t in -π..π,
      cexp (-(t * k * I)) * ∏ i ∈ s, charFun ((P.map (X i)).map (Int.cast : ℤ → ℝ)) t := by
  have mS : AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P := Finset.aemeasurable_fun_sum _ mX
  have hcast : Measurable (Int.cast : ℤ → ℝ) := measurable_of_countable _
  have hreal : (P.map fun ω ↦ ∑ i ∈ s, X i ω).map (Int.cast : ℤ → ℝ) =
      P.map fun ω ↦ ∑ i ∈ s, (X i ω : ℝ) := by
    rw [AEMeasurable.map_map_of_aemeasurable hcast.aemeasurable mS]
    congr 1 with ω
    simp
  have hprod := iIndepFun.charFun_map_fun_finsetSum_eq_prod (s := s)
    (X := fun i ω ↦ (X i ω : ℝ)) (fun i hi ↦ hcast.comp_aemeasurable (mX i hi))
    (hX.comp (fun _ ↦ (Int.cast : ℤ → ℝ)) fun _ ↦ hcast)
  have hS : P.real {ω | ∑ i ∈ s, X i ω = k} = (P.map fun ω ↦ ∑ i ∈ s, X i ω).real {k} := by
    rw [map_measureReal_apply_of_aemeasurable mS (measurableSet_singleton k)]
    simp only [Set.preimage, Set.mem_singleton_iff]
  rw [hS, measureReal_singleton_eq_integral_charFun_map_intCast, hreal, hprod]
  congr 2 with t
  simp only [Finset.prod_apply]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [AEMeasurable.map_map_of_aemeasurable hcast.aemeasurable (mX i hi), Function.comp_def]

/-- **Inversion for a sum of independent identically distributed integer random variables.** If
the `X i` are independent and distributed as `X 0`, with `φ` the characteristic function of the
law of `X 0`, then `P(X 0 + ⋯ + X (n - 1) = k) = (2π)⁻¹ ∫_{-π}^{π} exp(-i t k) φ(t)ⁿ dt`. -/
theorem iIndepFun.measureReal_sum_range_eq_integral_charFun_pow {X : ℕ → Ω → ℤ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (k : ℤ) :
    (P.real {ω | ∑ i ∈ Finset.range n, X i ω = k} : ℂ) = (2 * π : ℂ)⁻¹ * ∫ t in -π..π,
      cexp (-(t * k * I)) * charFun ((P.map (X 0)).map (Int.cast : ℤ → ℝ)) t ^ n := by
  rw [(hindep.restrict _).measureReal_sum_eq_integral_prod_charFun
    (fun i _ ↦ (hident i).aemeasurable_fst)]
  simp [(hident _).map_eq]

end ProbabilityTheory
