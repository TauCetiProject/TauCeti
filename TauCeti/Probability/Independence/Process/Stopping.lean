/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.Process.HasIndepIncrements
public import TauCeti.Probability.Process.Restart

/-!
# Restarting stationary count increments at a stopping time

For a right-continuous count process with stationary independent increments, the increment
over a fixed duration after a stopping time has its original law, independently of the stopped
natural history, on the event of finiteness. Path regularity is required only almost surely,
and neither completeness nor right continuity of the natural filtration is assumed.

This scalar event identity determines the next waiting time at successive arrivals of a
Poisson process. No independence from an enlarged filtration is asserted.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press (2018), Chapter 7, the exponential interarrival characterization.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- **The stopping-time restart identity for stationary independent count increments.**
On the finite-time event, an increment of duration `t` after a stopping time has the same law
as `N t`, independently of the stopped natural history. The stopping time may be infinite;
no fallback value at infinity enters the assertion. -/
theorem HasIndepIncrements.measure_inter_stoppedValue_sub_mem
    (hN : HasIndepIncrements N P) (hm : ∀ t, Measurable (N t))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t => N t ω))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s)
    (hstat : ∀ s t, IdentDistrib (fun ω => N (s + t) ω - N s ω) (N t) P P)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural N (fun t => (hm t).stronglyMeasurable)) τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (t : ℝ≥0) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * P (N t ⁻¹' B) := by
  have : IsProbabilityMeasure P := hN.isProbabilityMeasure
  let ℱ := Filtration.natural N (fun t => (hm t).stronglyMeasurable)
  have hdet (s : ℝ≥0) (C : Set Ω) (hC : MeasurableSet[ℱ s] C)
      (D : Set ℕ) (hD : MeasurableSet D) :
      P (C ∩ (fun ω => N (s + t) ω - N s ω) ⁻¹' D) = P C * P (N t ⁻¹' D) := by
    have hi := (hN.indepFun_shift_nat hm h0 hmono s).comp
      (measurable_pi_apply t) measurable_id
    have hind : Indep (ℱ s)
        (MeasurableSpace.comap (fun ω => N (s + t) ω - N s ω) inferInstance) P := by
      rw [Filtration.natural_eq_comap]
      exact hi.symm
    rw [(hind.indepSet_of_measurableSet hC
      ((comap_measurable _) hD)).measure_inter_eq_mul]
    rw [(hstat s t).measure_mem_eq hD]
  have hright : ∀ᵐ ω ∂P, ∀ s,
      ContinuousWithinAt (fun u => N (u + t) ω - N u ω) (Ici s) s := by
    filter_upwards [hrc] with ω hω s
    have hadd : Continuous (fun u : ℝ≥0 => u + t) := continuous_id.add continuous_const
    exact ((hω (s + t)).comp (f := fun u : ℝ≥0 => u + t)
      (x := s) (s := Ici s) hadd.continuousWithinAt
      (fun u hu => add_le_add hu (le_refl t))).sub (hω _)
  have h := hτ.measure_inter_stoppedValue_mem (U := fun s ω => N (s + t) ω - N s ω)
    (μ := P.map (N t)) (B := B) (fun s => (hm _).sub (hm _)) hright
    (fun s C hC D hD => by rw [Measure.map_apply (hm t) hD]; exact hdet s C hC D hD)
    hA .of_discrete
  simpa only [Measure.map_apply (hm t) .of_discrete] using h

end ProbabilityTheory
