/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMeasure.LaplaceFunctional
public import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Laplace functionals of independent superpositions

The Laplace functional of a countable sum of independent random measures is the product
of their Laplace functionals. No local finiteness or moment assumption is needed: infinite
integrals are allowed, with negative exponential zero. Finite partial superpositions
converge at the level of Laplace functionals even without independence.

In particular, the Poisson exponential formula is preserved by countable independent
superposition, with the intensity measures added. This permits assembling finite-intensity
pieces into a random measure of infinite total intensity, without an integrability
assumption on the test function.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 3–4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {ι Ω X : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : ι → Ω → Measure X} {f : X → ℝ≥0∞}

/-- Finite partial superpositions converge in Laplace functional to the countable
superposition. Independence, local finiteness, and finite test integrals are not required. -/
theorem tendsto_laplaceFunctional_finset_sum [IsFiniteMeasure P]
    (hN : ∀ i, Measurable (N i)) (hf : Measurable f) :
    Tendsto (fun s : Finset ι ↦ P.laplaceFunctional (fun ω ↦ ∑ i ∈ s, N i ω) f)
      atTop (𝓝 (P.laplaceFunctional (fun ω ↦ Measure.sum (fun i ↦ N i ω)) f)) := by
  simp only [laplaceFunctional_def, lintegral_finsetSum_measure, lintegral_sum_measure]
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ 1)
  · exact Filter.Eventually.of_forall fun s ↦
      measurable_coe_nnreal_ennreal.comp (ENNReal.measurable_expNeg.comp
        (Finset.measurable_sum s fun i _ ↦ (measurable_lintegral hf).comp (hN i)))
  · exact Filter.Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦
      ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
  · simp
  · exact ae_of_all _ fun ω ↦
      (ENNReal.continuous_coe.comp ENNReal.continuous_expNeg).continuousAt.tendsto.comp
        CompleteLattice.summable.hasSum

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {ι Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : ι → Ω → Measure X} {f : X → ℝ≥0∞}

/-- A finite independent superposition has the product Laplace functional. -/
theorem iIndepFun.laplaceFunctional_finset_sum (hind : iIndepFun N P)
    (hN : ∀ i, Measurable (N i)) (hf : Measurable f) (s : Finset ι) :
    P.laplaceFunctional (fun ω ↦ ∑ i ∈ s, N i ω) f =
      ∏ i ∈ s, P.laplaceFunctional (N i) f := by
  simp only [Measure.laplaceFunctional_def, lintegral_finsetSum_measure,
    ENNReal.expNeg_sum, ENNReal.ofNNReal_finsetProd]
  exact lintegral_prod_eq_prod_lintegral_of_indepFun s _
    (hind.comp (fun _ μ ↦ (ENNReal.expNeg (∫⁻ x, f x ∂μ) : ℝ≥0∞))
      (fun _ ↦ Measure.measurable_expNeg_lintegral measurable_id hf))
    (fun i ↦ Measure.measurable_expNeg_lintegral (hN i) hf)

/-- A countable independent superposition has the infinite-product Laplace functional.
The product exists even when it vanishes. -/
theorem iIndepFun.laplaceFunctional_sum [Countable ι] (hind : iIndepFun N P)
    (hN : ∀ i, Measurable (N i)) (hf : Measurable f) :
    P.laplaceFunctional (fun ω ↦ Measure.sum (fun i ↦ N i ω)) f =
      ∏' i, P.laplaceFunctional (N i) f := by
  have := hind.isProbabilityMeasure
  have hlim := Measure.tendsto_laplaceFunctional_finset_sum (P := P) hN hf
  simp_rw [hind.laplaceFunctional_finset_sum hN hf] at hlim
  exact tendsto_nhds_unique hlim (ENNReal.multipliable_of_le_one
    (fun i ↦ (Measure.laplaceFunctional_le P (N i) f).trans_eq (measure_univ))).hasProd

/-- Countable independent superposition preserves the Poisson exponential formula.
This statement needs neither finite total intensity nor finite test integrals. -/
theorem iIndepFun.laplaceFunctional_sum_eq_expNeg [Countable ι] (hind : iIndepFun N P)
    (hN : ∀ i, Measurable (N i)) {Λ : ι → Measure X} (hf : Measurable f)
    (hL : ∀ i, P.laplaceFunctional (N i) f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ i) : ℝ≥0∞)) :
    P.laplaceFunctional (fun ω ↦ Measure.sum (fun i ↦ N i ω)) f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞)
        ∂Measure.sum Λ) : ℝ≥0∞) := by
  rw [hind.laplaceFunctional_sum hN hf, lintegral_sum_measure, ENNReal.coe_expNeg_tsum]
  exact tprod_congr hL

end ProbabilityTheory
