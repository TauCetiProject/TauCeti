/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.Process.Stopping
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson increments after a stopping time

A nondecreasing, right-continuous count process starting at zero with independent Poisson
increments has fresh Poisson increments after any stopping time for its natural filtration.
The event identity retains the finite-time event explicitly and allows rate zero. It is the
conditional count identity used to obtain exponential waiting times after successive arrivals.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press (2018), Chapter 7.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- **Fresh Poisson increments at a stopping time.** On the finite-time event, the count
over a fixed duration after a natural-filtration stopping time has its usual Poisson law,
independently of the stopped history. Monotonicity and right continuity are only almost-sure
path assumptions; the rate may be zero and the stopping time may be infinite. -/
theorem HasIndepIncrements.measure_inter_stoppedValue_sub_mem_of_hasLaw_poissonMeasure
    (hN : HasIndepIncrements N P) (hm : ∀ t, Measurable (N t))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t => N t ω))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s) (r : ℝ≥0)
    (hlaw : ∀ s u, s ≤ u → HasLaw (fun ω => N u ω - N s ω)
      (poissonMeasure (r * (u - s))) P)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural N (fun t => (hm t).stronglyMeasurable)) τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (t : ℝ≥0) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * poissonMeasure (r * t) B := by
  have hmarg (u : ℝ≥0) : HasLaw (N u) (poissonMeasure (r * u)) P := by
    have h := hlaw 0 u bot_le
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [h0] with ω hω using by simp [hω]
  have hstat (s u : ℝ≥0) :
      IdentDistrib (fun ω => N (s + u) ω - N s ω) (N u) P P := by
    have h := hlaw s (s + u) le_self_add
    rw [add_tsub_cancel_left] at h
    exact h.identDistrib (hmarg u)
  rw [hN.measure_inter_stoppedValue_sub_mem hm h0 hmono hrc hstat hτ hA t B,
    ← Measure.map_apply (hm t) .of_discrete, (hmarg t).map_eq]

end ProbabilityTheory
