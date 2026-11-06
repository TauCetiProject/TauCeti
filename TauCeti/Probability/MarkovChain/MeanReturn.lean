/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Recurrence
public import TauCeti.Probability.MarkovChain.ReturnGaps
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Extended mean first-return times

The mean positive return time is an extended nonnegative integral. In particular,
a positive probability of never returning forces infinite mean; it is not lost
by converting an infinite hitting time to a natural or real number. At a recurrent
state this mean agrees with the extended mean of every return gap, so renewal
laws of large numbers apply even when the mean return time is infinite.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.7.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] (κ : Kernel S S) [IsMarkovKernel κ]

/-- The extended mean of the first return starting at time one. Nonreturn is infinity. -/
def meanReturnTime (x : S) : ℝ≥0∞ :=
  ∫⁻ ω, (hittingAfter (fun n ω => ω n) {x} 1 ω).map ((↑) : ℕ → ℝ≥0)
    ∂markovChainLaw (Measure.dirac x) κ

/-- Evaluation of the extended mean positive return time. -/
theorem meanReturnTime_def (x : S) : κ.meanReturnTime x =
    ∫⁻ ω, (hittingAfter (fun n ω => ω n) {x} 1 ω).map ((↑) : ℕ → ℝ≥0)
      ∂markovChainLaw (Measure.dirac x) κ := (rfl)

/-- The positive first-return mean is at least one, including for a transient state. -/
theorem one_le_meanReturnTime (x : S) : 1 ≤ κ.meanReturnTime x := by
  calc
    1 = ∫⁻ _ω, (1 : ℝ≥0∞) ∂markovChainLaw (Measure.dirac x) κ := by simp
    _ ≤ κ.meanReturnTime x := lintegral_mono fun ω => by
      have hτ := le_hittingAfter (u := fun n (ω : ℕ → S) => ω n) (s := {x}) (n := 1) ω
      induction h : hittingAfter (fun n (ω : ℕ → S) => ω n) {x} 1 ω
          using WithTop.recTopCoe with
      | top => exact le_top
      | coe n =>
        have hn : 1 ≤ n := by simpa only [h, ← WithTop.coe_one, WithTop.coe_le_coe] using hτ
        simpa only [WithTop.map_coe, ENNReal.some_eq_coe', ENNReal.coe_natCast,
          Nat.cast_one] using
          (Nat.cast_le (α := ℝ≥0∞)).mpr hn

variable [MeasurableSingletonClass S] {κ} {x : S}

/-- Finite extended mean return time implies almost-sure return. -/
theorem isRecurrent_of_meanReturnTime_ne_top (h : κ.meanReturnTime x ≠ ∞) :
    κ.IsRecurrent x := by
  have hm := (Filtration.adapted_piLE.isStoppingTime_hittingAfter
    (f := Filtration.piLE (X := fun _ : ℕ => S))
    (s := {x}) (n := 1) (measurableSet_singleton x)).measurable'
  have hfinite := ae_lt_top ((measurable_of_countable
    (fun t : WithTop ℕ => (t.map ((↑) : ℕ → ℝ≥0) : ℝ≥0∞))).comp hm) h
  have hE : MeasurableSet {ω : ℕ → S | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} :=
    ((measurableSet_singleton ⊤).preimage hm).compl
  apply isRecurrent_iff.mpr
  apply (mem_ae_iff_prob_eq_one hE).mp
  filter_upwards [hfinite] with ω hω
  exact fun ht => hω.ne (by simp only [Function.comp_apply, ht]; rfl)

/-- At a transient state the positive return time has infinite extended mean. -/
theorem IsTransient.meanReturnTime_eq_top (hx : κ.IsTransient x) :
    κ.meanReturnTime x = ∞ := by
  by_contra h
  exact (isTransient_iff.mp hx) (isRecurrent_of_meanReturnTime_ne_top h)

variable [Countable S]

/-- At a recurrent state every return gap has the extended mean positive return time.
This equality remains valid for infinite mean. -/
theorem IsRecurrent.lintegral_returnGap (hx : κ.IsRecurrent x) (k : ℕ) :
    ∫⁻ ω, (returnGap (fun n (ω : ℕ → S) => ω n) x k ω : ℝ≥0∞)
      ∂markovChainLaw (Measure.dirac x) κ = κ.meanReturnTime x := by
  have hid : HasLaw (id : (ℕ → S) → (ℕ → S))
      (markovChainLaw (Measure.dirac x) κ) (markovChainLaw (Measure.dirac x) κ) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hgap := hid.natCast_returnGap_map_hittingAfter (isRecurrent_iff.mp hx) k
  have hm : Measurable (fun t : WithTop ℕ => (t.map ((↑) : ℕ → ℝ≥0) : ℝ≥0∞)) :=
    measurable_of_countable _
  have hmean := hgap.lintegral_comp hm.aemeasurable
  rw [lintegral_map' hm.aemeasurable] at hmean
  · simpa only [Function.comp_def, id_eq, Nat.cast_withTop, WithTop.map_coe,
      ENNReal.some_eq_coe', ENNReal.coe_natCast, meanReturnTime_def] using hmean
  · exact (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => S))
      (s := {x}) (n := 1) (measurableSet_singleton x)).measurable'.aemeasurable

end ProbabilityTheory.Kernel
