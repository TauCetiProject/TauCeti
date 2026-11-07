/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Recurrence
public import TauCeti.Probability.MarkovChain.ReturnGaps

/-!
# Extended means of return gaps

At a recurrent state the extended mean positive return time agrees with the
extended mean of every return gap, so renewal laws of large numbers apply even
when the mean return time is infinite. The mean return time itself is defined in
`TauCeti.Probability.MarkovChain.Recurrence` and retains infinity on nonreturn.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.7.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  {κ : Kernel S S} [IsMarkovKernel κ] {x : S}

/-- Finite extended mean return time implies almost-sure return. -/
theorem isRecurrent_of_meanReturnTime_ne_top (h : κ.meanReturnTime x ≠ ∞) :
    κ.IsRecurrent x := by
  by_contra hx
  exact h ((isTransient_iff.mpr hx).meanReturnTime_eq_top)

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
  have hm : Measurable (fun t : WithTop ℕ => ENat.toENNReal t) :=
    measurable_of_countable _
  have hmean := hgap.lintegral_comp hm.aemeasurable
  rw [lintegral_map' hm.aemeasurable] at hmean
  · have hcast (n : ℕ) : ENat.toENNReal (n : WithTop ℕ) = (n : ℝ≥0∞) :=
      ENat.toENNReal_coe n
    simpa only [Function.comp_def, id_eq, hcast, meanReturnTime_def] using hmean
  · exact (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => S))
      (s := {x}) (n := 1) (measurableSet_singleton x)).measurable'.aemeasurable

end ProbabilityTheory.Kernel
