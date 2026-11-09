/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.RandomMeasure.LaplaceFunctional
import TauCeti.Probability.Distributions.Poisson.Laplace
import Mathlib.Probability.Independence.Integration

/-!
# Laplace functional of a Poisson random measure

The independent-count definition implies the exponential Laplace formula for every measurable
extended nonnegative test. Infinite test integrals and atoms of the intensity are allowed.
The formula identifies the functionals used to assemble Poisson laws from independent pieces.

The argument follows G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge
University Press, 2018, Theorem 3.9: first use disjoint level sets, then monotone approximation
and a finite-intensity exhaustion.
-/

public section

open Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X}

private theorem poisson_laplace_simple [IsFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) (f : SimpleFunc X ℝ≥0∞) :
    P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  classical
  let e := Fintype.equivFin f.range
  let A (i : f.range) : Set X := f ⁻¹' {i.val}
  have hm (i : f.range) : MeasurableSet (A i) := f.measurableSet_preimage _
  have hi : iIndepFun (fun i : f.range => fun ω => N ω (A i)) P := by
    apply iIndepFun.of_precomp e.symm.surjective
    exact h.iIndepFun (fun i => hm (e.symm i)) (fun _ => measure_lt_top _ _)
      (fun i j hij => (Set.disjoint_singleton.mpr
        (fun heq => hij (e.symm.injective (Subtype.ext heq)))).preimage f)
  have heval (μ : Measure X) : ∫⁻ x, f x ∂μ = ∑ i : f.range, i.val * μ (A i) := by
    rw [f.lintegral_eq_lintegral, SimpleFunc.lintegral]
    exact (Finset.sum_coe_sort f.range (fun y => y * μ (f ⁻¹' {y}))).symm
  have htransform (i : f.range) :
      ∫⁻ ω, (ENNReal.expNeg (i.val * N ω (A i)) : ℝ≥0∞) ∂P =
        (ENNReal.expNeg (Λ (A i) * (1 - (ENNReal.expNeg i.val : ℝ≥0∞))) : ℝ≥0∞) := by
    rw [(h.hasLaw (hm i) (measure_lt_top _ _)).lintegral_comp
      (f := fun t => (ENNReal.expNeg (i.val * t) : ℝ≥0∞)) (by fun_prop),
      lintegral_map (by fun_prop) Measurable.of_discrete,
      lintegral_expNeg_mul_natCast_poissonMeasure, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  rw [Measure.laplaceFunctional_def]
  simp_rw [heval, ENNReal.expNeg_sum, ENNReal.ofNNReal_finsetProd]
  have hmeas (i : f.range) :
      Measurable (fun ω => (ENNReal.expNeg (i.val * N ω (A i)) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (ENNReal.measurable_expNeg.comp
      (measurable_const.mul ((Measure.measurable_coe (hm i)).comp h.measurable)))
  have hi' : iIndepFun (fun i : f.range => fun ω =>
      (ENNReal.expNeg (i.val * N ω (A i)) : ℝ≥0∞)) P := by
    simpa only [Function.comp_def] using
      hi.comp (fun i => fun t => (ENNReal.expNeg (i.val * t) : ℝ≥0∞)) (fun _ => by fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi' hmeas]
  simp_rw [htransform]
  rw [← ENNReal.ofNNReal_finsetProd, ← ENNReal.expNeg_sum]
  congr 2
  have hmap := (f.map (fun t => 1 - (ENNReal.expNeg t : ℝ≥0∞))).lintegral_eq_lintegral Λ
  simp only [SimpleFunc.map_apply] at hmap
  rw [hmap, SimpleFunc.map_lintegral,
    ← Finset.sum_coe_sort f.range (fun t => (1 - (ENNReal.expNeg t : ℝ≥0∞)) * Λ (f ⁻¹' {t}))]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private theorem poisson_laplace_monotone [IsProbabilityMeasure P]
    (hN : Measurable N) {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f)
    (hformula : ∀ n, P.laplaceFunctional N (f n) =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f n x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞)) :
    P.laplaceFunctional N (fun x => ⨆ n, f n x) =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (⨆ n, f n x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  have hl := Measure.tendsto_laplaceFunctional_iSup (P := P) hN hf hmono
  simp_rw [hformula] at hl
  apply tendsto_nhds_unique hl
  apply ENNReal.continuous_coe.continuousAt.tendsto.comp
  apply ENNReal.continuous_expNeg.continuousAt.tendsto.comp
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    fun_prop
  · filter_upwards [] with x m n hmn
    exact tsub_le_tsub_left (ENNReal.coe_le_coe.mpr
      (ENNReal.antitone_expNeg (hmono hmn x))) 1
  · filter_upwards [] with x
    exact (ENNReal.continuous_sub_left (by simp)).continuousAt.tendsto.comp
      ((ENNReal.continuous_coe.comp ENNReal.continuous_expNeg).continuousAt.tendsto.comp
        (tendsto_atTop_iSup (fun m n hmn => hmono hmn x)))

private theorem poisson_laplace_finite [IsFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  let := h.isProbabilityMeasure
  simpa only [SimpleFunc.iSup_eapprox_apply hf] using
    poisson_laplace_monotone h.measurable (fun n => (SimpleFunc.eapprox f n).measurable)
      (SimpleFunc.monotone_eapprox f) (fun n => poisson_laplace_simple h (SimpleFunc.eapprox f n))

/-- The exponential Laplace formula for a Poisson random measure with sigma-finite intensity.
The test may take the value `∞`; no moment or atomlessness hypothesis is required. -/
theorem IsPoissonRandomMeasure.laplaceFunctional_eq_expNeg [SigmaFinite Λ]
    (h : IsPoissonRandomMeasure P N Λ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  classical
  let := h.isProbabilityMeasure
  let g (n : ℕ) := (spanningSets Λ n).indicator f
  have hg (n : ℕ) : Measurable (g n) := hf.indicator (measurableSet_spanningSets Λ n)
  have hmono : Monotone g := fun _ _ hmn =>
    Set.indicator_le_indicator_of_subset (spanningSets_mono hmn) (fun _ => bot_le)
  have hsup : (fun x => ⨆ n, g n x) = f := by
    funext x
    apply le_antisymm
    · exact iSup_le fun n => Set.indicator_le_self (spanningSets Λ n) f x
    · exact le_iSup_of_le (spanningSetsIndex Λ x) (by simp [g, mem_spanningSetsIndex])
  rw [← hsup]
  apply poisson_laplace_monotone h.measurable hg hmono
  intro n
  let : IsFiniteMeasure (Λ.restrict (spanningSets Λ n)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top Λ n).ne
  have hn := poisson_laplace_finite (h.restrict (measurableSet_spanningSets Λ n)) hf
  rw [Measure.laplaceFunctional_restrict _ _ (measurableSet_spanningSets Λ n)] at hn
  convert hn using 2
  congr 1
  rw [← lintegral_indicator (measurableSet_spanningSets Λ n)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ spanningSets Λ n <;> simp [g, hx]

end TauCeti.Probability
