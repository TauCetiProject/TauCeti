/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.EntranceLimits
public import TauCeti.Probability.MarkovChain.MeanReturn
public import TauCeti.Probability.Process.Excursion.MarkovChain
public import TauCeti.Probability.Renewal.StrongLaw

/-!
# Occupation frequency from the counted state

For a chain started at `x`, the fraction of times `1, …, n` spent at `x`
converges almost surely to the reciprocal extended mean positive return time.
The reciprocal is taken in `ℝ≥0∞` before conversion to `ℝ`. Thus both transient
states and recurrent states with infinite mean have limiting frequency zero.
The expectations have the same limit by bounded convergence. These assertions
also transfer to arbitrary realizations with the specified path law.

The recurrent case consumes the independent-excursion decomposition
`TauCeti.Probability.iIndepFun_excursionProcess` and the renewal strong law.
An excursion omits its closing return step, so its length plus one is the
renewal increment. No integrability of the return time is assumed.

Writing `r_y = (m_y⁻¹).toReal` with `m_y = κ.meanReturnTime y`, the limit holds at every state
with no recurrence hypothesis: started at `y`, the occupation frequency of `y` converges almost
surely to `r_y` (`ProbabilityTheory.Kernel.ae_tendsto_visitCount_div_markovChainLaw_dirac`), since
at a transient state the visits are almost surely finite and `m_y = ∞`. The first-entrance
transfer then gives the limit from any finite initial law
(`MeasureTheory.Measure.ae_tendsto_visitCount_div_markovChainLaw`) and the limit of the mean
occupation frequency (`MeasureTheory.Measure.tendsto_integral_visitCount_div_markovChainLaw`).

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.10, Theorem 1.10.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open TauCeti TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

private theorem IsRecurrent.ae_tendsto_visitCount_succ_div (hy : κ.IsRecurrent y) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  -- Excursion lengths plus their closing return steps form an i.i.d. renewal process.
  let P := markovChainLaw (Measure.dirac y) κ
  let E := excursionProcess (fun n (x : ℕ → α) => x n) y
  let T (k : ℕ) (x : ℕ → α) : ℝ≥0 := (E k x).length + 1
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac (isRecurrent_iff.mp hy)
  have h0 := markovChainLaw_dirac_ae_apply_zero κ y
  have hEm (k : ℕ) : Measurable (E k) := by
    have he : E k = fun x => excursion x y k := funext fun x => excursionProcess_apply _ _ _ _
    rw [he]
    exact measurable_excursion y k (measurableSet_singleton y)
  have hlen : Measurable (fun e : List α => ((e.length : ℝ≥0) + 1)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0))).comp
      measurable_list_length |>.add_const 1
  have hi : ProbabilityTheory.iIndepFun T P :=
    (iIndepFun_excursionProcess hret).comp _ (fun _ => hlen)
  have hid (k : ℕ) : IdentDistrib (T k) (T 0) P P := by
    apply IdentDistrib.comp _ hlen
    refine ⟨(hEm k).aemeasurable, (hEm 0).aemeasurable, ?_⟩
    exact (map_excursionProcess_eq_excursionLaw k
      (hret.mono fun x hx => exists_visitCount_of_infinite hx (k + 1))).trans
      (map_excursionProcess_eq_excursionLaw 0
        (hret.mono fun x hx => exists_visitCount_of_infinite hx 1)).symm
  have hz : P {x | T 0 x = 0} < 1 := by
    have : {x | T 0 x = 0} = ∅ := by ext x; simp [T]
    simp [this]
  -- On recurrent paths its arrivals are exactly the enumerated visits, starting at zero.
  have harr : ∀ᵐ x ∂P, ∀ k, arrival T k x = (visitTime x y k : ℝ≥0) := by
    filter_upwards [hret, h0] with x hx hx0 k
    have hs : ∑ i ∈ Finset.range k, ((excursion x y i).length + 1) = visitTime x y k := by
      induction k with
      | zero => simp [visitTime_zero_of_eq hx0]
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hstep := loopSteps_excursionPrefix_of_infinite_of_zero hx hx0 (k + 1)
        rw [excursionPrefix_succ, loopSteps_append,
          loopSteps_excursionPrefix_of_infinite_of_zero hx hx0 k] at hstep
        simpa only [loopSteps_cons, loopSteps_nil, add_zero] using hstep
    simpa only [arrival_def, T, E, excursionProcess_apply, Nat.cast_sum,
      Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : ℝ≥0)) hs
  -- The first increment is the specified positive return, not the entrance at time zero.
  have hmean : (∫⁻ x, (T 0 x : ℝ≥0∞) ∂P) = κ.meanReturnTime y := by
    rw [meanReturnTime_def]
    apply lintegral_congr_ae
    filter_upwards [harr, h0, hret] with x hx hx0 hxret
    have hvisit := successiveVisit_eq_visitTime (X := fun n (x : ℕ → α) => x n)
      (exists_visitCount_of_infinite hxret 1)
    rw [successiveVisit_one_eq_hittingAfter_of_zero hx0] at hvisit
    rw [hvisit]
    have hcast (n : ℕ) : ENat.toENNReal (n : WithTop ℕ) = (n : ℝ≥0∞) :=
      ENat.toENNReal_coe n
    simpa only [arrival_def, Finset.sum_range_one, hcast, ENNReal.coe_natCast] using
      congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (hx 1)
  -- Invert the renewal strong law and identify its count with positive-time occupation.
  have hLLN := ae_tendsto_renewalCountNat_div (T := T) (fun _ _ h => hi.indepFun h) hid hz
  rw [hmean] at hLLN
  filter_upwards [hLLN, ae_tendsto_arrival_atTop (T := T) hi hid hz, harr, hret, h0]
    with x hx hnonexp hxarr hxret hx0
  have hcount (n : ℕ) : renewalCountNat T (n : ℝ≥0) x =
      visitCount (fun k => x (k + 1)) y n := by
    apply eq_of_forall_le_iff
    intro k
    rw [le_renewalCountNat_iff hnonexp, hxarr]
    have hvisit := successiveVisit_eq_visitTime (X := fun n (x : ℕ → α) => x n)
      (exists_visitCount_of_infinite hxret k)
    have hc := successiveVisit_le_iff (X := fun n (x : ℕ → α) => x n)
      (a := y) (k := k) (ω := x) (n := n)
    rw [hvisit] at hc
    have hsplit := visitCount_add x y 1 n
    rw [Nat.add_comm 1 n] at hsplit
    simp only [visitCount_succ_of_eq hx0, visitCount_zero, zero_add] at hsplit
    simpa only [Nat.cast_le, hsplit, Nat.add_comm 1, Nat.lt_add_one_iff] using hc
  simpa only [Function.comp_def, hcount, NNReal.coe_natCast] using
    hx.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))

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

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] {P : Measure Ω}
  {X : Ω → ℕ → α} {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

/-- The occupation limit transfers to every realization with the same path law.
No topology or canonical-space assumption is imposed on the sample space. -/
theorem ae_tendsto_visitCount_succ_div
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  have h := κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- Expected occupation fractions have the same limit. Bounded convergence applies
also to transient states and recurrent states with infinite mean return time. -/
theorem tendsto_integral_visitCount_succ_div
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  classical
  let : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hm (n : ℕ) : Measurable (fun x : ℕ → α =>
      (visitCount (fun k => x (k + 1)) y n : ℝ) / n) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_visitCount_comp y n (measurableSet_singleton y)
        (fun i _ => measurable_pi_apply (i + 1)))).div_const n
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
      (integrable_const 1) hb hX.ae_tendsto_visitCount_succ_div

end ProbabilityTheory.HasLaw

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

/-- **Long-run occupation frequencies.** From any finite initial law, the
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

end MeasureTheory.Measure
