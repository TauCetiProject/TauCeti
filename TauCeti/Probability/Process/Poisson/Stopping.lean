/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.Process.Stopping
public import Mathlib.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Process.Poisson.Characterization

/-!
# Poisson increments after a stopping time

A nondecreasing, right-continuous count process starting at zero with independent Poisson
increments has fresh Poisson increments after any stopping time for its natural filtration.
The event identity retains the finite-time event explicitly and allows rate zero. It is the
conditional count identity used to obtain exponential waiting times after successive arrivals.
A filtration-relative version also applies when deterministic increment independence is given
explicitly, without a zero-start or monotonicity assumption.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press (2018), Chapter 7.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

/-- Poisson increments independent of a filtration's deterministic histories retain their
Poisson law at a stopping time, independently of the stopped history on the finite-time
event. No zero-start or monotonicity assumption is needed when independence is supplied. -/
theorem measure_inter_stoppedValue_sub_preimage_eq_mul_of_hasLaw_poissonMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {N : ℝ≥0 → Ω → ℕ} {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hm : ∀ s, Measurable (N s))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s)
    (r t : ℝ≥0)
    (hindep : ∀ s, Indep
      (MeasurableSpace.comap (fun ω => N (s + t) ω - N s ω) inferInstance) (ℱ s) P)
    (hlaw : ∀ s u, s ≤ u → HasLaw (fun ω => N u ω - N s ω)
      (poissonMeasure (r * (u - s))) P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * poissonMeasure (r * t) B := by
  exact hτ.measure_inter_stoppedValue_sub_preimage_eq_mul hm hrc t hindep
    (fun s => by simpa only [add_tsub_cancel_left] using hlaw s (s + t) le_self_add) hA B

end MeasureTheory.IsStoppingTime

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- **Fresh Poisson increments at a stopping time.** On the finite-time event, the count
over a fixed duration after a stopping time for a subfiltration of the natural filtration
has its usual Poisson law, independently of the stopped history. Monotonicity and right
continuity are only almost-sure path assumptions; the rate may be zero and the stopping time
may be infinite. -/
theorem HasIndepIncrements.measure_inter_stoppedValue_sub_preimage_eq_mul_of_hasLaw_poissonMeasure
    (hN : HasIndepIncrements N P) (hm : ∀ t, Measurable (N t))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t => N t ω))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s) (r : ℝ≥0)
    (hlaw : ∀ s u, s ≤ u → HasLaw (fun ω => N u ω - N s ω)
      (poissonMeasure (r * (u - s))) P)
    {ℱ : Filtration ℝ≥0 mΩ}
    (hle : ℱ ≤ Filtration.natural N (fun s => (hm s).stronglyMeasurable))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (t : ℝ≥0) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * poissonMeasure (r * t) B := by
  have hmarg (u : ℝ≥0) : HasLaw (N u) (poissonMeasure (r * u)) P := by
    have h := hlaw 0 u bot_le
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [h0] with ω hω using by simp [hω]
  rw [hN.measure_inter_stoppedValue_sub_preimage_eq_mul hm h0 hmono hrc t
    (fun s => TauCeti.Probability.identDistrib_sub_of_hasLaw_poissonMeasure hlaw hmarg s t)
    hle hτ hA B,
    ← Measure.map_apply (hm t) .of_discrete, (hmarg t).map_eq]

end ProbabilityTheory
