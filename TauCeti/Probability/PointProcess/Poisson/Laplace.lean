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
and exhaustion by positive level sets. An infinite-intensity positive level forces both
sides to vanish, so the intensity need not be sigma-finite.
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

private theorem poisson_laplace_infinite_level
    (h : IsPoissonRandomMeasure P N Λ) {f : X → ℝ≥0∞} (hf : Measurable f)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hΛ : Λ {x | c ≤ f x} = ∞) :
    P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  have hA : MeasurableSet {x | c ≤ f x} := measurableSet_le measurable_const hf
  have hcount : P.laplaceFunctional N f = 0 := by
    rw [Measure.laplaceFunctional_def]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [h.ae_eq_top hA hΛ] with ω hω
    have hbound := mul_meas_ge_le_lintegral (μ := N ω) hf c
    simp only [hω, ENNReal.mul_top hc] at hbound
    simp [top_unique hbound]
  have hpos : (ENNReal.expNeg c : ℝ≥0∞) < 1 := by
    rw [ENNReal.coe_expNeg, EReal.exp_lt_one_iff]
    exact EReal.neg_lt_zero.mpr (EReal.coe_ennreal_pos_iff_ne_zero.mpr hc)
  have hbound : (1 - (ENNReal.expNeg c : ℝ≥0∞)) * Λ {x | c ≤ f x} ≤
      ∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ := by
    rw [← lintegral_indicator_const hA]
    apply lintegral_mono
    intro x
    by_cases hx : c ≤ f x
    · simpa [hx] using tsub_le_tsub_left
        (ENNReal.coe_le_coe.mpr (ENNReal.antitone_expNeg hx)) 1
    · simp [hx]
  rw [hΛ, ENNReal.mul_top (ne_of_gt (tsub_pos_iff_lt.mpr hpos))] at hbound
  simp [hcount, top_unique hbound]

/-- The exponential Laplace formula for a Poisson random measure with arbitrary intensity.
The test may take the value `∞`; no moment or atomlessness hypothesis is required. -/
theorem IsPoissonRandomMeasure.laplaceFunctional_eq_expNeg
    (h : IsPoissonRandomMeasure P N Λ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  classical
  let := h.isProbabilityMeasure
  let A (n : ℕ) := {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ f x}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le measurable_const hf
  by_cases hfin : ∀ n, Λ (A n) < ∞
  swap
  · obtain ⟨n, hn⟩ := not_forall.mp hfin
    exact poisson_laplace_infinite_level h hf (by simp)
      (top_unique (not_lt.mp hn))
  let g (n : ℕ) := (A n).indicator f
  have hg (n : ℕ) : Measurable (g n) := hf.indicator (hA n)
  have hmono : Monotone g := fun _ _ hmn =>
    Set.indicator_le_indicator_of_subset
      (fun x hx => (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hmn 1)).trans hx)
      (fun _ => bot_le)
  have hsup : (fun x => ⨆ n, g n x) = f := by
    funext x
    apply le_antisymm
    · exact iSup_le fun n => Set.indicator_le_self (A n) f x
    · by_cases hx : f x = 0
      · simp [hx]
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
      have hxn : x ∈ A n :=
        (ENNReal.inv_le_inv.mpr (le_add_of_nonneg_right zero_le)).trans hn.le
      exact le_iSup_of_le n (by simp [g, hxn])
  rw [← hsup]
  apply poisson_laplace_monotone h.measurable hg hmono
  intro n
  let : IsFiniteMeasure (Λ.restrict (A n)) := isFiniteMeasure_restrict.mpr (hfin n).ne
  have hn := poisson_laplace_finite (h.restrict (hA n)) hf
  rw [Measure.laplaceFunctional_restrict _ _ (hA n)] at hn
  convert hn using 2
  congr 1
  rw [← lintegral_indicator (hA n)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A n <;> simp [g, hx]

end TauCeti.Probability
