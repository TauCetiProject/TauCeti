/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Process.Excursion.MarkovChain
public import TauCeti.Probability.Process.Occupation
public import TauCeti.Probability.Renewal.StrongLaw

/-!
# Occupation frequencies at a recurrent state

For a chain started at a state to which it returns almost surely, the fraction of positive
times spent at that state converges almost surely to the reciprocal extended mean return time.
The inverse is taken in `ℝ≥0∞` before conversion to `ℝ`; in particular the frequency is zero
when the mean return time is infinite.

For a chain started from a point mass, the expected number of visits to any target state
at times one through `n` is the sum of the corresponding transition probabilities.
This identity requires neither recurrence nor countability.

The proof consumes the independent-excursion decomposition
`TauCeti.Probability.iIndepFun_excursionProcess` and the renewal strong law. An excursion
omits its closing return step, so its length plus one is the renewal increment. Visits at time
zero are not included in the occupation count.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open TauCeti TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- The expected number of visits to `y` at times one through `n`, starting from `x`,
is the sum of the corresponding transition probabilities. -/
theorem integral_visitCount_succ_markovChainLaw_dirac (x y : α) (n : ℕ) :
    (∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ)
      ∂markovChainLaw (Measure.dirac x) κ) =
      ∑ i ∈ Finset.range n, ((κ ^ (i + 1)) x).real {y} := by
  rw [integral_visitCount (fun i (ω : ℕ → α) => ω (i + 1))
    (fun i => measurable_pi_apply (i + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Measure.real, Measure.markovChainLaw_setOf_apply_eq_comp,
    Measure.dirac_bind (κ ^ (i + 1)).measurable]

variable [Countable α] {y : α}

/-- **The occupation law of large numbers at a recurrent starting state.** The proportion of
positive times through `n` spent at `y` converges to the reciprocal extended mean first return.
No integrability assumption is needed: infinite mean gives frequency zero. -/
theorem ae_tendsto_visitCount_div_of_return_eq_one
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (∫⁻ x, (hittingAfter (fun n x => x n) {y} 1 x).recTopCoe ⊤
          (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (Measure.dirac y) κ)⁻¹.toReal) := by
  -- Excursion lengths plus their closing return steps form an i.i.d. renewal process.
  let P := markovChainLaw (Measure.dirac y) κ
  let E := excursionProcess (fun n (x : ℕ → α) => x n) y
  let T (k : ℕ) (x : ℕ → α) : ℝ≥0 := (E k x).length + 1
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac hy
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
  have hmean : (∫⁻ x, (T 0 x : ℝ≥0∞) ∂P) =
      ∫⁻ x, (hittingAfter (fun n x => x n) {y} 1 x).recTopCoe ⊤
        (fun n => (n : ℝ≥0∞)) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [harr, h0, hret] with x hx hx0 hxret
    have hvisit := successiveVisit_eq_visitTime (X := fun n (x : ℕ → α) => x n)
      (exists_visitCount_of_infinite hxret 1)
    rw [successiveVisit_one_eq_hittingAfter_of_zero hx0] at hvisit
    rw [hvisit]
    simpa only [arrival_def, Finset.sum_range_one, Nat.cast_withTop,
      WithTop.recTopCoe_coe, ENNReal.coe_natCast] using congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (hx 1)
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

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] {P : Measure Ω}
  {X : Ω → ℕ → α} {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

/-- The recurrent-state occupation limit transfers to every realization with the same path
law. No topology or canonical-space assumption is imposed on the sample space. -/
theorem ae_tendsto_visitCount_div_of_return_eq_one
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (∫⁻ x, (hittingAfter (fun n x => x n) {y} 1 x).recTopCoe ⊤
          (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (Measure.dirac y) κ)⁻¹.toReal) := by
  have h := κ.ae_tendsto_visitCount_div_of_return_eq_one hy
  nth_rw 2 [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- Expected occupation fractions have the same recurrent-state limit. Bounded convergence
applies even when the mean return time is infinite. -/
theorem tendsto_integral_visitCount_div_of_return_eq_one
    (hX : HasLaw X (markovChainLaw (Measure.dirac y) κ) P)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P) atTop
      (𝓝 (∫⁻ x, (hittingAfter (fun n x => x n) {y} 1 x).recTopCoe ⊤
        (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (Measure.dirac y) κ)⁻¹.toReal) := by
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
      (integrable_const 1) hb (hX.ae_tendsto_visitCount_div_of_return_eq_one hy)

end ProbabilityTheory.HasLaw
