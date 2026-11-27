/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.EntranceLimits
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.ReturnGaps
public import TauCeti.Probability.Process.Occupation
public import TauCeti.Probability.Process.ReturnGapRenewal
public import TauCeti.Probability.Renewal.StrongLaw

/-!
# Occupation frequency from the counted state

For a chain started at `x`, the fraction of times `1, …, n` spent at `x`
converges almost surely to the reciprocal extended mean positive return time.
The reciprocal is taken in `ℝ≥0∞` before conversion to `ℝ`. Thus both transient
states and recurrent states with infinite mean have limiting frequency zero.
The expectations have the same limit by bounded convergence. These assertions
also transfer to arbitrary realizations with the specified path law.

The recurrent case consumes the independent return-gap laws and identifies their
renewal count with positive-time visits. The renewal strong law then gives the
limit without any integrability assumption on the return time.

For a chain started from a point mass, the expected number of visits to any target state
at times one through `n` is the sum of the corresponding transition probabilities.
This identity requires neither recurrence nor countability.

Writing `r_y = (m_y⁻¹).toReal` with `m_y = κ.meanReturnTime y`, the limit holds at every state
with no recurrence hypothesis: started at `y`, the occupation frequency of `y` converges almost
surely to `r_y` (`ProbabilityTheory.Kernel.ae_tendsto_visitCount_div_markovChainLaw_dirac`), since
at a transient state the visits are almost surely finite and `m_y = ∞`. The first-entrance
transfer then gives the almost-sure limit from any initial law
(`MeasureTheory.Measure.ae_tendsto_visitCount_div_markovChainLaw`,
`ProbabilityTheory.HasLaw.ae_tendsto_visitCount_div_markovChainLaw`) and, from any finite initial
law, the limit of the mean occupation frequency
(`MeasureTheory.Measure.tendsto_integral_visitCount_div_markovChainLaw`,
`ProbabilityTheory.HasLaw.tendsto_integral_visitCount_div_markovChainLaw`); started at `y`, this
gives the Cesàro limit of the positive-time return probabilities
(`ProbabilityTheory.Kernel.tendsto_cesaro_pow_real_singleton_self`). Consequently, positive
recurrence is equivalent to a strictly positive expected or almost-sure limiting visit fraction
starting from `y`
(`ProbabilityTheory.Kernel.isPositiveRecurrent_iff_exists_pos_tendsto_integral_visitCount_div`,
`ProbabilityTheory.Kernel.isPositiveRecurrent_iff_exists_pos_ae_tendsto_visitCount_div`), and for
non-positive-recurrent states the visit fraction and its expectation tend to zero from any
initial law (`MeasureTheory.Measure.ae_tendsto_visitCount_div_zero_of_not_isPositiveRecurrent`,
`MeasureTheory.Measure.tendsto_integral_visitCount_div_zero_of_not_isPositiveRecurrent`, and their
`ProbabilityTheory.HasLaw` counterparts).

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.10, Theorem 1.10.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open TauCeti TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The expected number of visits to `y` at times one through `n`, starting from `x`,
is the sum of the corresponding transition probabilities. -/
theorem integral_visitCount_succ_markovChainLaw_dirac (κ : Kernel α α) [IsMarkovKernel κ]
    (x y : α) (n : ℕ) :
    (∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ)
      ∂markovChainLaw (Measure.dirac x) κ) =
      ∑ i ∈ Finset.range n, ((κ ^ (i + 1)) x).real {y} := by
  rw [integral_visitCount (fun i (ω : ℕ → α) => ω (i + 1))
    (fun i => measurable_pi_apply (i + 1))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Measure.real, Measure.markovChainLaw_setOf_apply_eq_comp,
    Measure.dirac_bind (κ ^ (i + 1)).measurable]

variable [Countable α] {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

private theorem IsRecurrent.ae_tendsto_visitCount_succ_div (hy : κ.IsRecurrent y) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  -- Independent return gaps give the renewal increments and their extended mean.
  let P := markovChainLaw (Measure.dirac y) κ
  let T (k : ℕ) (x : ℕ → α) : ℝ≥0 := returnGap (fun n x => x n) y k x
  have hrec := isRecurrent_iff.mp hy
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac hrec
  have h0 := markovChainLaw_dirac_ae_apply_zero κ y
  have hcast : Measurable (fun n : ℕ => (n : ℝ≥0)) := measurable_of_countable _
  have hi : ProbabilityTheory.iIndepFun T P :=
    (κ.iIndepFun_returnGap hrec).comp _ (fun _ => hcast)
  have hid (k : ℕ) : IdentDistrib (T k) (T 0) P P :=
    ((κ.hasLaw_returnGap hrec k).identDistrib (κ.hasLaw_returnGap hrec 0)).comp hcast
  have hmean : (∫⁻ x, (T 0 x : ℝ≥0∞) ∂P) = κ.meanReturnTime y := by
    simpa only [T, ENNReal.coe_natCast] using hy.lintegral_returnGap 0
  have hLLN := ae_tendsto_renewalCountNat_div (T := T) (fun _ _ h => hi.indepFun h) hid
  rw [hmean] at hLLN
  -- The deterministic adapter excludes the initial visit and includes time n.
  filter_upwards [hLLN, hret, h0] with x hx hxret hx0
  simpa only [Function.comp_def, T,
    renewalCountNat_returnGap (X := fun n (x : ℕ → α) => x n) hxret hx0,
    NNReal.coe_natCast] using hx.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))

/-- **Occupation strong law from the counted state.** The positive-time visit frequency
converges to the reciprocal extended mean first-return time, without any finite-mean
assumption. Transient and infinite-mean recurrent states both have frequency zero. -/
theorem ae_tendsto_visitCount_div_markovChainLaw_dirac (κ : Kernel α α)
    [IsMarkovKernel κ] (y : α) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n)
        atTop (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  classical
  by_cases hy : κ.IsRecurrent y
  · exact hy.ae_tendsto_visitCount_succ_div
  · have htrans : κ.IsTransient y := isTransient_iff.mpr hy
    rw [htrans.meanReturnTime_eq_top, ENNReal.inv_top, ENNReal.toReal_zero]
    have hfinite : ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ, {n | x n = y}.Finite := by
      simpa only [ae_iff, Set.Infinite] using
        Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero (Measure.dirac y) κ
          (isTransient_iff_return_probability_lt_one.mp htrans)
    filter_upwards [hfinite] with x hx
    have hf : {k | x (k + 1) = y}.Finite :=
      hx.preimage (fun _ _ _ _ hij => Nat.add_right_cancel hij)
    apply squeeze_zero (fun n => by positivity) _
      (tendsto_const_div_atTop_nhds_zero_nat (hf.toFinset.card : ℝ))
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (by
      rw [visitCount_eq_count]
      exact Nat.count_le_card hf n)

end ProbabilityTheory.Kernel

private theorem measurable_visitCount_succ_div {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α) (n : ℕ) :
    Measurable (fun x : ℕ → α => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) :=
  ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_visitCount_comp y n (measurableSet_singleton y)
      (fun i _ => measurable_pi_apply (i + 1)))).div_const n

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] {P : Measure Ω}
  {X : Ω → ℕ → α} {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

/-- The occupation limit transfers to every realization with the same path law.
No topology or canonical-space assumption is imposed on the sample space. -/
theorem ae_tendsto_visitCount_div_markovChainLaw_dirac
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  have h := κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- Expected occupation fractions have the same limit. Bounded convergence applies
also to transient states and recurrent states with infinite mean return time. -/
theorem tendsto_integral_visitCount_div_markovChainLaw_dirac
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  classical
  let : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hm := measurable_visitCount_succ_div y
  have hb (n : ℕ) : ∀ᵐ ω ∂P,
      ‖(visitCount (fun k => X ω (k + 1)) y n : ℝ) / n‖ ≤ 1 := by
    apply Eventually.of_forall
    intro ω
    by_cases hn : n = 0
    · simp [hn]
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).2
      exact_mod_cast (by
        rw [visitCount_eq_count]
        exact Nat.count_le (fun k => X ω (k + 1) = y))
  simpa only [Function.comp_def, integral_const, probReal_univ, one_smul] using
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((hm n).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable)
      (integrable_const 1) hb hX.ae_tendsto_visitCount_div_markovChainLaw_dirac

end ProbabilityTheory.HasLaw

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Started at `y`, the expected positive-time visit fraction converges to the real reciprocal mean
return time `(κ.meanReturnTime y)⁻¹.toReal`. -/
theorem tendsto_integral_visitCount_div_markovChainLaw_dirac (κ : Kernel α α) [IsMarkovKernel κ]
    (y : α) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
        ∂markovChainLaw (Measure.dirac y) κ)
      atTop (𝓝 (κ.meanReturnTime y)⁻¹.toReal) :=
  (HasLaw.id
    (μ := markovChainLaw (Measure.dirac y) κ)).tendsto_integral_visitCount_div_markovChainLaw_dirac

/-- The Cesàro averages of the positive-time return probabilities `((κ ^ (i + 1)) y).real {y}`
converge to `(κ.meanReturnTime y)⁻¹.toReal`. -/
theorem tendsto_cesaro_pow_real_singleton_self (κ : Kernel α α) [IsMarkovKernel κ] (y : α) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, ((κ ^ (i + 1)) y).real {y}) / n)
      atTop (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  simpa only [integral_div, κ.integral_visitCount_succ_markovChainLaw_dirac] using
    κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y

/-- **Expected occupation characterization of positive recurrence.** A state `y` is positive
recurrent if and only if its expected positive-time visit fraction starting from `y` converges to a
strictly positive limit. -/
theorem isPositiveRecurrent_iff_exists_pos_tendsto_integral_visitCount_div
    {κ : Kernel α α} [IsMarkovKernel κ] {y : α} :
    κ.IsPositiveRecurrent y ↔
      ∃ r > 0, Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
        ∂markovChainLaw (Measure.dirac y) κ) atTop (𝓝 r) := by
  rw [← inv_meanReturnTime_toReal_pos_iff]
  refine ⟨fun hpos => ⟨_, hpos, κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y⟩, ?_⟩
  rintro ⟨r, hr, hlim⟩
  exact (tendsto_nhds_unique (κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y) hlim) ▸ hr

/-- **Almost-sure occupation characterization of positive recurrence.** A state `y` is positive
recurrent if and only if, starting from `y`, its positive-time visit fraction converges almost
surely to a strictly positive deterministic limit. -/
theorem isPositiveRecurrent_iff_exists_pos_ae_tendsto_visitCount_div
    {κ : Kernel α α} [IsMarkovKernel κ] {y : α} :
    κ.IsPositiveRecurrent y ↔
      ∃ r > 0, ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ,
        Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 r) := by
  rw [← inv_meanReturnTime_toReal_pos_iff]
  refine ⟨fun hpos => ⟨_, hpos, κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y⟩, ?_⟩
  rintro ⟨r, hr, hae⟩
  obtain ⟨ω, hω₁, hω₂⟩ := ((κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y).and hae).exists
  exact (tendsto_nhds_unique hω₁ hω₂) ▸ hr

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

omit [IsFiniteMeasure ν] in
/-- **Long-run occupation frequencies.** From any initial law, the
proportion `V_y(n) / n` of the times `1, …, n` spent at `y` converges almost surely to
`r_y = (m_y⁻¹).toReal` on the event that the chain enters `y`, and to zero off that event. -/
theorem ae_tendsto_visitCount_div_markovChainLaw (y : α) :
    ∀ᵐ x ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (if hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ then
          (κ.meanReturnTime y)⁻¹.toReal else 0)) :=
  ae_tendsto_visitCount_div_of_ae_tendsto_dirac ν κ
    (κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y)

/-- **Mean occupation frequencies.** From any finite initial law, the mean proportion of the times
`1, …, n` spent at `y` converges to `ℙ(H_y < ∞) * r_y`, where `H_y` is the first entrance time to
`y` and `r_y = (m_y⁻¹).toReal`. -/
theorem tendsto_integral_visitCount_div_markovChainLaw (y : α) :
    Tendsto (fun n : ℕ => ∫ x, (visitCount (fun k => x (k + 1)) y n : ℝ) / n
        ∂markovChainLaw ν κ) atTop
      (𝓝 ((markovChainLaw ν κ).real {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} *
        (κ.meanReturnTime y)⁻¹.toReal)) :=
  tendsto_integral_visitCount_div_of_ae_tendsto_dirac ν κ
    (κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y)

omit [IsFiniteMeasure ν] in
/-- From any initial measure `ν`, the positive-time visit fraction at a non-positive-recurrent
state tends to zero almost surely. -/
theorem ae_tendsto_visitCount_div_zero_of_not_isPositiveRecurrent {y : α}
    (hy : ¬ κ.IsPositiveRecurrent y) :
    ∀ᵐ ω ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  have h0 : (κ.meanReturnTime y)⁻¹.toReal = 0 := Kernel.inv_meanReturnTime_toReal_eq_zero_iff.mpr hy
  simpa only [h0, ite_self] using ν.ae_tendsto_visitCount_div_markovChainLaw κ y

/-- From any finite initial measure `ν`, the expected positive-time visit fraction at a
non-positive-recurrent state tends to zero. -/
theorem tendsto_integral_visitCount_div_zero_of_not_isPositiveRecurrent {y : α}
    (hy : ¬ κ.IsPositiveRecurrent y) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
        ∂markovChainLaw ν κ) atTop (𝓝 0) := by
  have h0 : (κ.meanReturnTime y)⁻¹.toReal = 0 := Kernel.inv_meanReturnTime_toReal_eq_zero_iff.mpr hy
  simpa only [h0, mul_zero] using ν.tendsto_integral_visitCount_div_markovChainLaw κ y

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] {P : Measure Ω}
  {X : Ω → ℕ → α} {ν : Measure α} {κ : Kernel α α} [IsMarkovKernel κ]

/-- **Long-run occupation frequencies on any realization.** On any realization of a Markov chain
from any initial law `ν`, the proportion `V_y(n) / n` of the times `1, …, n` spent at `y`
converges almost surely to `(κ.meanReturnTime y)⁻¹.toReal` on the event that the chain enters `y`,
and to zero off that event. -/
theorem ae_tendsto_visitCount_div_markovChainLaw
    (hX : HasLaw X (markovChainLaw ν κ) P) (y : α) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (if hittingAfter (fun n ω => X ω n) {y} 0 ω ≠ ⊤ then
          (κ.meanReturnTime y)⁻¹.toReal else 0)) := by
  have h := ν.ae_tendsto_visitCount_div_markovChainLaw κ y
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- **Mean occupation frequencies on any realization.** On any realization of a Markov chain from a
finite initial law `ν`, the expected proportion of the times `1, …, n` spent at `y` converges to
`P.real {ω | H_y(ω) < ∞} * (κ.meanReturnTime y)⁻¹.toReal`. -/
theorem tendsto_integral_visitCount_div_markovChainLaw [IsFiniteMeasure ν]
    (hX : HasLaw X (markovChainLaw ν κ) P) (y : α) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P) atTop
      (𝓝 (P.real {ω | hittingAfter (fun n ω => X ω n) {y} 0 ω ≠ ⊤} *
        (κ.meanReturnTime y)⁻¹.toReal)) := by
  have heq (n : ℕ) :
      (∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P) =
        ∫ x, (visitCount (fun k => x (k + 1)) y n : ℝ) / n ∂markovChainLaw ν κ := by
    simpa only [Function.comp_apply] using
      hX.integral_comp (measurable_visitCount_succ_div y n).aestronglyMeasurable
  have hE : MeasurableSet {x : ℕ → α | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0
  have hreal : P.real {ω | hittingAfter (fun n ω => X ω n) {y} 0 ω ≠ ⊤} =
      (markovChainLaw ν κ).real {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} :=
    hX.measureReal_eq hE
  simp_rw [heq, hreal]
  exact ν.tendsto_integral_visitCount_div_markovChainLaw κ y

/-- On any realization of a Markov chain from any initial law `ν`, the positive-time visit fraction
at a non-positive-recurrent state tends to zero almost surely. -/
theorem ae_tendsto_visitCount_div_zero_of_not_isPositiveRecurrent {y : α}
    (hX : HasLaw X (markovChainLaw ν κ) P) (hy : ¬ κ.IsPositiveRecurrent y) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  have h0 : (κ.meanReturnTime y)⁻¹.toReal = 0 := Kernel.inv_meanReturnTime_toReal_eq_zero_iff.mpr hy
  simpa only [h0, ite_self] using hX.ae_tendsto_visitCount_div_markovChainLaw y

/-- On any realization of a Markov chain from a finite initial law `ν`, the expected positive-time
visit fraction at a non-positive-recurrent state tends to zero. -/
theorem tendsto_integral_visitCount_div_zero_of_not_isPositiveRecurrent [IsFiniteMeasure ν] {y : α}
    (hX : HasLaw X (markovChainLaw ν κ) P) (hy : ¬ κ.IsPositiveRecurrent y) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P)
      atTop (𝓝 0) := by
  have h0 : (κ.meanReturnTime y)⁻¹.toReal = 0 := Kernel.inv_meanReturnTime_toReal_eq_zero_iff.mpr hy
  simpa only [h0, mul_zero] using hX.tendsto_integral_visitCount_div_markovChainLaw y

end ProbabilityTheory.HasLaw
