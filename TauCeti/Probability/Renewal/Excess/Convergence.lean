/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Excess.Limit
public import TauCeti.Probability.Renewal.Excess.Lattice

/-!
# The limiting excess-life theorem

For i.i.d. nonnegative increments with nonlattice law and finite extended mean, the
excess life converges to the equilibrium excess-life distribution. Its distribution
function is the integrated interarrival tail divided by the mean, and its density
and normalization are given by `MeasureTheory.Measure.equilibriumExcessLaw`.
The distributional conclusion holds as time tends to infinity and for any realization
of the limiting law. Precomposition with `MeasureTheory.TendstoInDistribution.comp_tendsto`
gives convergence along any filter of observation times tending to infinity.

With infinite extended mean, the probability of any bounded excess tends to zero,
whether the increment law is lattice or nonlattice. This is escape to infinity in
probability, not convergence in distribution to the zero measure.

All results allow atoms at zero and arbitrary measurable sample spaces.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

-- Collect the representative choices and transport facts needed by the limit proofs below.
private theorem exists_measurable_renewalExcess (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    ∃ T' : ℕ → Ω → ℝ≥0, (∀ n, Measurable (T' n)) ∧ iIndepFun T' P ∧
      (∀ n, IdentDistrib (T' n) (T' 0) P P) ∧ P.map (T' 0) = P.map (T 0) ∧
      ∀ t, renewalExcess T' t =ᵐ[P] renewalExcess T t := by
  let T' : ℕ → Ω → ℝ≥0 := fun n ↦ (hid n).aemeasurable_fst.mk (T n)
  have heq (n : ℕ) : T n =ᵐ[P] T' n := (hid n).aemeasurable_fst.ae_eq_mk
  refine ⟨T', fun n ↦ (hid n).aemeasurable_fst.measurable_mk, hindep.congr heq,
    fun n ↦ ?_, Measure.map_congr (heq 0).symm,
    fun t ↦ (renewalExcess_congr_ae heq t).symm⟩
  exact ((hid n).aemeasurable_fst.identDistrib_mk.symm.trans (hid n)).trans
    (hid 0).aemeasurable_fst.identDistrib_mk

/-- **The limiting excess-life distribution function.** For nonlattice i.i.d. increments,
the probability of an excess at most `x` tends to the normalized integrated interarrival
tail, with limit zero when the extended mean is infinite. The formula includes `x = 0`
and allows zero increments; nonlatticeness implies that the extended mean is positive. -/
theorem tendsto_measureReal_renewalExcess_le_of_not_isLattice
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), (P.map (T 0)).real {u | s < (u : ℝ)})) := by
  wlog hT : ∀ n, Measurable (T n) generalizing T
  · obtain ⟨T', hT', hindep', hid', hmap, heq⟩ := exists_measurable_renewalExcess hindep hid
    have hlim := this hindep' hid' (by rwa [hmap]) hT'
    simp only [hmap] at hlim
    convert hlim using 1
    ext t
    exact measureReal_congr ((heq t).symm.mono fun ω hω ↦ by
      simp only [mem_ofPred_eq, hω])
  have := hindep.isProbabilityMeasure
  have hzero := Measure.measure_setOf_eq_zero_lt_one_of_not_isLattice
    (hT 0).aemeasurable hNL
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul]
    apply tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
      hT hindep hid hzero x
    simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul] using
      (P.map (T 0)).tendsto_renewalFunction_add_sub hNL x
  · rw [← Measure.equilibriumExcessLaw_real_Iic]
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
      hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **The limiting excess-life law.** For nonlattice i.i.d. increments with finite
extended mean, the real-valued excess converges in distribution to any realization
of the equilibrium excess-life probability law as time tends to infinity. Precomposition
with `MeasureTheory.TendstoInDistribution.comp_tendsto` gives convergence along any
filter of observation times tending to infinity. -/
theorem tendstoInDistribution_renewalExcess_of_not_isLattice
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun (t : ℝ≥0) ω ↦ (renewalExcess T t ω : ℝ)) atTop
      Z (fun _ ↦ P) Q := by
  wlog hT : ∀ n, Measurable (T n) generalizing T
  · obtain ⟨T', hT', hindep', hid', hmap, heq⟩ := exists_measurable_renewalExcess hindep hid
    have hlim := this hindep' hid' (by rwa [hmap]) (by rwa [hmap]) (by rwa [hmap]) hT'
    exact hlim.congr (fun t ↦ (heq t).mono fun ω hω ↦ congrArg ((↑) : ℝ≥0 → ℝ) hω)
      EventuallyEq.rfl
  have hzero := Measure.measure_setOf_eq_zero_lt_one_of_not_isLattice
    (hT 0).aemeasurable hNL
  exact tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ tendsto_id

/-- **Infinite-mean excess escape.** For i.i.d. nonnegative increments of infinite
extended mean, the probability that the excess is at most any fixed threshold tends
to zero. No lattice or nonlattice hypothesis is needed, and observation times range
over the entire nonnegative half-line. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  by_cases hL : (P.map (T 0)).IsLattice
  · obtain ⟨T', hT', hindep', hid', hmap, heq⟩ := exists_measurable_renewalExcess hindep hid
    have hlim := tendsto_measureReal_renewalExcess_le_of_isLattice_of_mean_eq_top
      hT' hindep' hid' (by rwa [hmap]) (by rwa [hmap]) x
    convert hlim using 1
    ext t
    exact measureReal_congr ((heq t).symm.mono fun ω hω ↦ by
      simp only [mem_ofPred_eq, hω])
  · simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul] using
      tendsto_measureReal_renewalExcess_le_of_not_isLattice hindep hid hL x

end TauCeti.Probability
